#!/usr/bin/env python3

# Copyright 2026 The Kubernetes Authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Localization outdatedness triage helper.

Compares each localized Markdown page against its English source and
classifies it as `Strong signal`, `Moderate signal`,
`Weak signal (lastmod only)`, or `No signal`.

New locale note:
    Locales under content/ are auto-discovered when scanning all locales.
    New locales should start with the default LocaleProfile. Add explicit
    calibration only after manual report review shows repeated
    locale-specific false positives or false negatives.

Usage:
    # Scan all non-en locales (default)
    python3 scripts/l10n-outdatedness-triage.py
    
    # Scan specific locales
    python3 scripts/l10n-outdatedness-triage.py --lang ko ja zh-cn
    
    # Show GitHub links + per-file indicator details
    python3 scripts/l10n-outdatedness-triage.py --lang ko --link web --verbose

    # Run with `--help` for the full option list.
    python3 scripts/l10n-outdatedness-triage.py --help
"""

import argparse
import datetime
import os
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass, field
from typing import Dict, FrozenSet, List, Optional, Set, Tuple

# --- Constants ---
# These thresholds are empirically set per locale; 
# a statistical approach (median+MAD from structurally-clean files)
# could replace them with auto-calibrated per-locale values.
_LENGTH_GAP_MIN_EN_LINES = 15      # EN files shorter than this skip all length-gap checks
_SHORT_EN_THRESHOLD = 40           # below this, length gap requires a companion indicator
_CJK_SHORT_EN_THRESHOLD = 56       # same guard for CJK (denser text, files run longer)
_LATIN_MIN_EN_LINES = 55           # Latin compactness guard activates only above this

# Empirical boundary: Latin false alarms sit at >=0.94, real ru mismatch at <=0.85.
_LATIN_BODY_RATIO_MIN = 0.90       # body-word ratio floor for "full translation" in Latin guard

_LENGTH_GAP_NONE = ""
_LENGTH_GAP_SILENT = "silent"
_LENGTH_GAP_SMALL = "small"
_LENGTH_GAP_MODERATE = "moderate"
_LENGTH_GAP_LARGE = "large"

# ASCII-only boundary — Python's `\b` treats CJK as word chars, so plain
# `\bv1\.\b` silently missed `v1.22以降` etc. Captures (major, minor) so
# future Kubernetes major versions compare correctly against v1.x.
_VERSION_RE = re.compile(r"(?<![A-Za-z0-9])v(\d+)\.(\d{1,3})(?!\d)")
_L10N_VERSION_RE = re.compile(
    r"(?<![A-Za-z0-9])v(\d+)\.(\d{1,3})(?!\d)|(?<![A-Za-z0-9.:/])(1)\.([1-4]\d)(?![.\d])"
)
_ANCHOR_RE = re.compile(r"\{#([^}]+)\}")
# Trailing `(?:\n|$)` (not a mandatory `\n`): a handful of upstream EN files
# have no trailing newline after the closing `---`, which used to make this
# fail to match at all -- front matter would then be counted as body text,
# producing spurious `empty_stub` flags on pages that are legitimately
# front-matter-only on both sides (e.g. section-index stubs relying on
# Hugo's auto-generated child listing).
_STRIP_FM = re.compile(r"^\s*---\s*\n.*?\n---\s*(?:\n|$)", re.DOTALL)
_STRIP_CODE = re.compile(r"```.*?```", re.DOTALL)
_STRIP_CMNT = re.compile(r"<!--.*?-->", re.DOTALL)
_STRIP_INLINE = re.compile(r"`[^`\n]+`")

# Unicode-aware body-word counter for the Latin-compactness check; keeps
# `informação` and Cyrillic words intact.
_BODY_WORD_RE = re.compile(r"[^\W_]{2,}", re.UNICODE)

_FS_VERSION_RE = re.compile(r'for_k8s_version="(v?\d+\.\d+)"')
_FS_GATE_RE = re.compile(r'feature_gate_name="([A-Za-z_][A-Za-z0-9_]*)"')
_FS_STATE_RE = re.compile(
    r'\{\{[<%][ \t]*-?feature_state\b[^}>%]*?\bstate="([A-Za-z]+)"', re.DOTALL
)
_FG_STAGE_BLOCK_RE = re.compile(
    r"^\s*-\s*stage:\s*(\S+)|^\s*(fromVersion|toVersion|defaultValue|removed):\s*\"?([^\"\n#]+)\"?",
    re.MULTILINE,
)
_APIVERSION_LINE_RE = re.compile(
    r"^[ \t]*-?[ \t]*apiVersion:\s*\"?([A-Za-z0-9./_-]+)\"?\s*$", re.MULTILINE
)
_KIND_LINE_RE = re.compile(
    r"^[ \t]*-?[ \t]*kind:\s*\"?([A-Z][A-Za-z0-9]+)\"?\s*$", re.MULTILINE
)
_IMAGE_TAG_LINE_RE = re.compile(
    r"^[ \t]*-?[ \t]*image:[ \t]*\"?([A-Za-z0-9._/-]+:[A-Za-z0-9._-]+)\"?[ \t]*(?:#.*)?$",
    re.MULTILINE,
)

_ORPHAN_SKIP_BASENAMES: FrozenSet[str] = frozenset({
    "README.md", "_search.md", "sitemap.md", "_redirects",
})
_ORPHAN_REASON = (
    "No English source found; verify whether this file was renamed/removed "
    "upstream or is intentionally locale-specific."
)

STATUS_STRONG_SIGNAL = "Strong signal"
STATUS_MODERATE_SIGNAL = "Moderate signal"
STATUS_LASTMOD_ONLY = "Weak signal (lastmod only)"
STATUS_NO_SIGNAL = "No signal"
_LASTMOD_ONLY_NOTE = (
    "English source has a newer git commit timestamp (`lastmod`) than the "
    "localized file, but no structural or token signal was found (may be minor "
    "typo/link edits or prose-only updates)."
)

# Cutoffs for when missing items count as a "strong" outdatedness signal;
# see classify_status() for how strong signals affect the final status.
_STRONG_H2_THRESHOLD = 2              # missing H2 headings
_STRONG_H3_WITH_H2_THRESHOLD = 5      # missing H3s, plus at least one missing H2
_STRONG_CODE_THRESHOLD = 3            # missing code blocks
_STRONG_ANCHOR_THRESHOLD = 5          # missing section anchors
_STRONG_VERSION_THRESHOLD = 3         # missing newer Kubernetes version refs

# Markup tokens that mark up structural/functional content (links, Hugo
# shortcodes, tables, URLs, key=value syntax) and should survive translation
# with a stable count regardless of language -- translation changes prose,
# not markup. A large swing in one of these usually means a link, shortcode,
# admonition block, or table row was dropped (or added) without the
# localized file following suit.
#
# ``` (code fences) is deliberately excluded: it's already tracked via
# missing_code_blocks/severe_code_loss/moderate_code_loss above, so counting
# it again here would double-book the same signal under a new name.
#
# Calibrated against 196 random `ko` files using git-history ground truth
# (EN has a commit after the localized file's own last real edit == truly
# outdated, independent of file-size or importance judgment calls): at
# rel>=0.25/abs>=2 this catches 61% of truly-outdated files at a 33% false
# -alarm rate on files EN has not touched at all since -- roughly the same
# reliability band as the other supporting indicators below, so it is wired
# in as a supporting/strong pair, never a standalone verdict.
#
# Known blind spot: this cannot detect a same-shape edit -- a link *target*
# changed but the brackets stayed, a version number bumped, a word swapped
# for another -- since none of that moves a token count. It also cannot
# validate pages whose real content lives in sibling resource-bundle files
# rather than the page body itself (e.g. feature-gates/index.md, which reads
# from ~464 per-gate files); that class of gap needs a dedicated resource-set
# comparison, not a token-count diff.
#
# `:` is deliberately excluded from this body-prose set: ko (at least)
# systematically rewrites an English "lead-in clause ending in a colon,
# followed by a code block" (`Create the Deployment:`) as a complete Korean
# sentence ending in a period (`디플로이먼트를 생성한다.`) -- a real, repeated,
# purely stylistic pattern confirmed in-corpus, not drift. Colon still is a
# reliable, high-confidence signal in one narrower place: front-matter
# `key:` presence (see missing_front_matter_keys below), where there is no
# stylistic escape hatch -- the key line either exists or it doesn't.
# Raw inline emphasis chars (`*`, `_`) and `%` are deliberately excluded in
# favor of structural list-item tokens (`bullet_list`, `numbered_list`):
# CJK locales frequently replace `_italic_` / `**bold**` with corner brackets
# or plain text, Indonesian italicizes English technical terms (`_Pod_`), and
# non-Latin URLs introduce percent-encoded (`%EC%...`) sequences, whereas
# Hugo shortcodes (`{{% ... %}}`) are already captured by `{{` and `}}`.
_MARKUP_TOKENS: Tuple[str, ...] = (
    "[", "]", "bullet_list", "numbered_list", "{{", "}}", "<", ">", "http", "|", "=",
)
_BULLET_LIST_RE = re.compile(r"^[ \t]*[-*+][ \t]+", re.MULTILINE)
_BR_BULLET_RE = re.compile(r"<br\s*/?>[ \t]*-[ \t]+", re.IGNORECASE)
_CODE_TAG_RE = re.compile(r"<code>.*?</code>", re.DOTALL)
_REF_LINK_SECOND_BRACKET_RE = re.compile(r"\]\[[^\]]*\]")
_NUMBERED_LIST_RE = re.compile(r"^[ \t]*\d+[.)][ \t]+", re.MULTILINE)
_HTTP_URL_RE = re.compile(r"https?://", re.IGNORECASE)
_TOKEN_MISMATCH_REL_MIN = 0.25
_TOKEN_MISMATCH_ABS_MIN = 2
_STRONG_TOKEN_MISMATCH_THRESHOLD = 4  # distinct mismatching tokens for "severe"

# Front-matter keys that localized pages are allowed to omit or comment out
# by established convention:
# - `reviewers`, `approvers`: OWNERS-style English metadata omitted or
#   commented out in localized pages (see content/ko/AGENTS.md).
# - `auto_generated`: Localized reference/CLI pages are manually translated
#   and maintained; keeping `auto_generated: true` hides the "Edit this page"
#   button in `layouts/partials/page-meta-links.html`, so locales omit it.
# - `author`, `Author`, `authors`: Blog posts in locales such as `zh-cn`
#   retain the translated author byline (`**作者**：...`) in the body while
#   English retroactively migrated `author:` into front matter.
# - `url`: Legacy 2015-2018 English blog permalink pattern omitted in
#   localized blog posts in favor of `slug`.
# - `draft`: Explicit `draft: false` in English source is equivalent to
#   omitting `draft` in localized pages.
_OPTIONAL_FRONT_MATTER_KEYS: FrozenSet[str] = frozenset({
    "reviewers", "approvers", "auto_generated",
    "author", "Author", "authors",
    "url", "draft",
})
_FM_KEY_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_-]*):", re.MULTILINE)

# Denylist of front-matter keys whose values are either translated prose,
# locale-independent metadata, or multi-line YAML containers (handled via
# dedicated nested extractors). All other top-level scalar front-matter keys
# (e.g. `weight`, `content_type`, `id`, `min-kubernetes-server-version`,
# `full_link`, `type`, `layout`, `toc_hide`, `hide_summary`, `deprecated`,
# `removed`, and any future structural keys) must match between English and
# localized pages.
_TRANSLATABLE_FRONT_MATTER_KEYS: FrozenSet[str] = frozenset({
    "title", "Title", "linkTitle", "linktitle",
    "description", "Description", "short_description",
    "summary", "overview", "subheading", "heading_title_text",
    "manualLinkTitle", "quote",
})
_IGNORE_FRONT_MATTER_VALUE_KEYS: FrozenSet[str] = (
    _OPTIONAL_FRONT_MATTER_KEYS
    | _TRANSLATABLE_FRONT_MATTER_KEYS
    | frozenset({
        "slug", "aliases", "former_titles", "canonicalUrl", "translator",
        "date", "lastmod", "modified_time",
        "tags", "card", "cards", "menu", "stages", "api_metadata",
        "_build", "release_announcement", "feature", "sitemap",
        "related", "outputs", "resources",
    })
)
_FM_SCALAR_RE = re.compile(
    r"^([A-Za-z_][A-Za-z0-9_-]*):[ \t]*([^#\n]+?)[ \t]*(?:#.*)?$",
    re.MULTILINE,
)
_FM_NESTED_STRUCTURAL_RE = re.compile(
    r"^\s*(list|render|apiVersion|kind|import|major|minor|latest|ReleaseType):\s*\"?([^\"\n#]+?)\"?\s*(?:#.*)?$",
    re.MULTILINE,
)

# Denylist of Hugo shortcode attributes that hold translatable display prose
# or intentionally localized image/diagram paths (`src`, `image`, `link`).
# All other `key="value"` attributes across any shortcode (e.g. `term_id`,
# `page`, `file`, `lang`, `id`, `k8s-version`, `channel`, `type`, `path`,
# `url`, and any future shortcode identifiers) are compared structurally.
_TRANSLATABLE_SHORTCODE_ATTRS: FrozenSet[str] = frozenset({
    "text", "alt", "caption", "title", "name", "prepend", "summary", "attr",
    "src", "image", "link",
})
_POSITIONAL_SHORTCODE_NAMES: FrozenSet[str] = frozenset({
    "ref", "relref", "heading", "skew", "include", "param", "youtube",
})
_BARE_SHORTCODE_NAMES: FrozenSet[str] = frozenset({
    "caution", "warning", "thirdparty-content", "version-check",
})
_SHORTCODE_CALL_RE = re.compile(
    r"\{\{[<%][ \t]*(-?[A-Za-z0-9_/-]+)(.*?)[>%]\}\}", re.DOTALL
)
_TRACKED_INLINE_SHORTCODE_RE = re.compile(
    r"\{\{[<%][ \t]*-?(?:glossary_tooltip|glossary_definition|code_sample|codenew|code|"
    r"api-reference|page-api-reference|feature-state|feature_state|feature-gate-description|"
    r"include|heading|skew|param|ref|relref|figure|youtube)\b.*?[>%]\}\}",
    re.DOTALL,
)
_EXAMPLE_SHORTCODE_FILE_RE = re.compile(
    r'\{\{[<%][ \t]*-?(?:code_sample|codenew|code)\b[^>%\}]*\bfile="([^"]+)"[^>%\}]*[>%]\}\}',
    re.DOTALL,
)
_SHORTCODE_KV_RE = re.compile(r'([A-Za-z0-9_-]+)="([^"]*)"')
_MD_LINK_TARGET_RE = re.compile(
    r'\]\(\s*([^\s\)\"]+)\s*(?:\"[^\"]*\")?\s*\)|^\[[^\]]+\]:\s*(\S+)',
    re.MULTILINE,
)
_URL_LOCALE_PREFIX_RE = re.compile(
    r"^(https?://(?!(?:www\.)?github\.com/)[^/]+)?/[a-z]{2}(?:-[a-z]{2})?(?=/)"
)
_K8S_OFFICIAL_EXTERNAL_URL_RE = re.compile(
    r"^https?://(?:(?:www\.)?github\.com/(?:kubernetes|kubernetes-sigs|kubernetes-client|kubernetes-csi|cncf|etcd-io|containerd|cri-o|coredns)/|"
    r"(?:[a-z0-9-]+\.)*k8s\.io/)[^\s\)\"#?]+"
)
_CODE_SPAN_OR_BLOCK_RE = re.compile(
    r"```.*?```|`[^`\n]+`|<code>.*?</code>|<td\b[^>]*>.*?</td>", re.DOTALL
)
_CLI_FLAG_RE = re.compile(
    r"(?<![A-Za-z0-9_/-])(--[a-z][a-z0-9-]{1,40})(?![A-Za-z0-9_/-])"
)
_CLI_CMD_RE = re.compile(
    r"\b((?:dnf|yum|apt-get)[ \t]+(?:install|update|upgrade|downgrade|remove|list|config-manager)|"
    r"(?:kubectl|kubeadm|crictl)[ \t]+(?:apply|create|delete|get|describe|logs|exec|edit|patch|"
    r"rollout|scale|autoscale|cordon|drain|uncordon|taint|label|annotate|auth|debug|diff|events|"
    r"explain|expose|kustomize|port-forward|proxy|replace|run|set|top|wait|init|join|reset|token|"
    r"certs|kubeconfig|config|upgrade|alpha))\b"
)
_SYSCTL_OR_K8S_KEY_RE = re.compile(
    r"(?<![:/A-Za-z0-9_.-])((?:net\.ipv4|net\.ipv6|vm|fs|kernel)\.[a-z0-9_.-]+|"
    r"(?:[a-z0-9-]+\.)+kubernetes\.io/[a-z0-9._-]+|"
    r"kubernetes\.io/(?!docs\b|zh-|ko\b|ja\b|fr\b|de\b|es\b|pt-|ru\b|id\b|vi\b|pl\b|uk\b|bn\b|fa\b|hi\b|it\b)[a-z0-9._-]+)\b"
)
_STRONG_SHORTCODE_MISMATCH_THRESHOLD = 3
_STRONG_INTERNAL_LINK_MISMATCH_THRESHOLD = 4
_STRONG_CODE_IDENTIFIER_MISMATCH_THRESHOLD = 3

_STRONG_INDICATORS: FrozenSet[str] = frozenset({
    "empty_stub",
    "severe_heading_loss", "moderate_heading_loss",
    "severe_code_loss", "moderate_code_loss",
    "severe_version_mismatch", "moderate_version_mismatch",
    "severe_api_and_feature_mismatch", "moderate_api_or_feature_mismatch",
    "missing_front_matter_keys", "front_matter_value_mismatch",
    "severe_shortcode_mismatch", "moderate_shortcode_mismatch",
    "severe_internal_link_loss", "moderate_internal_link_loss",
    "severe_code_identifier_mismatch", "moderate_code_identifier_mismatch",
    "severe_example_file_mismatch", "moderate_example_file_mismatch",
    "severe_anchor_loss", "severe_markup_token_loss",
})
_SUPPORTING_INDICATORS: FrozenSet[str] = frozenset({
    "large_length_gap", "moderate_length_gap",
    "moderate_anchor_loss", "moderate_markup_token_loss",
})
# `small_length_gap` is excluded from `_SUPPORTING_INDICATORS`: it only
# triggers the dedicated possibly_outdated rule, never pairs with strong
# indicators or pads ≥3-supporting / large_length_gap promotions.
_LENGTH_GAP_INDICATORS: FrozenSet[str] = frozenset(
    {"large_length_gap", "moderate_length_gap", "small_length_gap"}
)
# Structural indicators (headings, code, anchors, versions, API tokens) —
# excludes length-gap indicators. Used as the corroboration gate for
# `small_length_gap` emission and for rule 4 in `classify_status`.
_NON_LENGTH_INDICATORS: FrozenSet[str] = frozenset({
    "moderate_heading_loss", "severe_heading_loss",
    "moderate_code_loss", "severe_code_loss",
    "moderate_anchor_loss", "severe_anchor_loss",
    "moderate_version_mismatch", "severe_version_mismatch",
    "severe_api_and_feature_mismatch", "moderate_api_or_feature_mismatch",
    "moderate_markup_token_loss", "severe_markup_token_loss",
    "missing_front_matter_keys", "front_matter_value_mismatch",
    "moderate_shortcode_mismatch", "severe_shortcode_mismatch",
    "moderate_internal_link_loss", "severe_internal_link_loss",
    "moderate_code_identifier_mismatch", "severe_code_identifier_mismatch",
    "moderate_example_file_mismatch", "severe_example_file_mismatch",
})

_STATUS_SORT_KEY = {
    STATUS_STRONG_SIGNAL: 0,
    STATUS_MODERATE_SIGNAL: 1,
    STATUS_LASTMOD_ONLY: 2,
    STATUS_NO_SIGNAL: 3,
}

# New locale calibration guide:
#
# - Locales under content/ are auto-discovered; adding a locale directory is
#   enough for the script to scan it.
# - Start with the default LocaleProfile. Add an explicit profile only to
#   record known properties such as script or text direction, or after manual
#   review shows repeated locale-specific false alarms / blindspots.
# - Suggested first run:
#     python3 scripts/l10n-outdatedness-triage.py --lang <locale> --verbose
# - Manually compare flagged localized files with their English sources, then
#   classify findings as real drift, false alarm, or mixed.
# - Add calibration only for repeated patterns, and document the reason in
#   the LocaleProfile notes field.

# --- Locale profiles ---

@dataclass(frozen=True)
class LocaleProfile:
    """Centralizes locale-specific calibration so adding a new locale is a
    single map entry rather than a scattering of conditionals."""

    script: str = "unknown"
    direction: str = "ltr"

    # Length-gap behavior
    short_en_threshold: int = _SHORT_EN_THRESHOLD
    min_en_lines_for_length_gap: int = _LENGTH_GAP_MIN_EN_LINES
    ignore_only_length_gap: bool = False

    # Optional compactness guard (Latin-script: word counts behave like EN)
    compactness_guard: bool = False
    compactness_min_en_lines: int = _LATIN_MIN_EN_LINES
    body_word_ratio_min: float = _LATIN_BODY_RATIO_MIN

    # Free-form note recording empirical rationale or future calibration plans.
    notes: str = ""


_DEFAULT_LOCALE_PROFILE = LocaleProfile()

_LOCALE_PROFILES: Dict[str, LocaleProfile] = {
    # CJK: denser glyphs run shorter at the same content volume, so raise
    # the short-EN floor before length gaps are trusted.
    "ko": LocaleProfile(script="cjk", short_en_threshold=_CJK_SHORT_EN_THRESHOLD),
    "ja": LocaleProfile(
        script="cjk",
        short_en_threshold=_CJK_SHORT_EN_THRESHOLD,
        ignore_only_length_gap=True,
        notes=(
            "Japanese can produce line-count-only false alarms because "
            "physical wrapping differs from English; non-length structural "
            "signals are still checked."
        ),
    ),
    "zh-cn": LocaleProfile(script="cjk", short_en_threshold=_CJK_SHORT_EN_THRESHOLD),
    "zh-tw": LocaleProfile(script="cjk", short_en_threshold=_CJK_SHORT_EN_THRESHOLD),

    # Latin-script locales whose word counts behave like EN's: full
    # translations run loose-wrapped at high body-word ratios.
    "pt-br": LocaleProfile(
        script="latin",
        compactness_guard=True,
        notes=(
            "Latin-script compactness guard can suppress line-count-only false "
            "alarms when a localized page has high body-word ratio, because "
            "full translations may wrap differently from English. Non-length "
            "structural signals are still checked."
        ),
    ),
    "es": LocaleProfile(
        script="latin",
        compactness_guard=True,
        notes=(
            "Latin-script compactness guard can suppress line-count-only false "
            "alarms when a localized page has high body-word ratio, because "
            "full translations may wrap differently from English. Non-length "
            "structural signals are still checked."
        ),
    ),
    "de": LocaleProfile(
        script="latin",
        compactness_guard=True,
        notes=(
            "Latin-script compactness guard can suppress line-count-only false "
            "alarms when a localized page has high body-word ratio, because "
            "full translations may wrap differently from English. Non-length "
            "structural signals are still checked."
        ),
    ),
    "fr": LocaleProfile(
        script="latin",
        compactness_guard=True,
        notes=(
            "Latin-script compactness guard can suppress line-count-only false "
            "alarms when a localized page has high body-word ratio, because "
            "full translations may wrap differently from English. Non-length "
            "structural signals are still checked."
        ),
    ),
    "it": LocaleProfile(
        script="latin",
        compactness_guard=True,
        notes=(
            "Latin-script compactness guard can suppress line-count-only false "
            "alarms when a localized page has high body-word ratio, because "
            "full translations may wrap differently from English. Non-length "
            "structural signals are still checked."
        ),
    ),

    # Cyrillic — explicitly opt out of the Latin compactness guard:
    # real ru/uk drift at the same pattern sits at notably lower body ratios.
    "ru": LocaleProfile(script="cyrillic"),
    "uk": LocaleProfile(script="cyrillic"),

    # Persian is the first RTL localization. Initial audit found no
    # RTL-specific parsing issue, so this records metadata only and does not
    # enable RTL-specific heuristics.
    "fa": LocaleProfile(script="arabic", direction="rtl"),
}


def get_locale_profile(locale: str) -> LocaleProfile:
    return _LOCALE_PROFILES.get(locale, _DEFAULT_LOCALE_PROFILE)


# --- Data classes ---

@dataclass(frozen=True)
class ParsedFile:
    visible_lines: int
    h2: int
    h3: int
    code_blocks: int
    anchors: FrozenSet[str]
    versions: FrozenSet[Tuple[int, int]]
    h4: int = 0
    body_words: int = 0
    paragraphs: int = 0
    feature_state_tokens: FrozenSet[str] = frozenset()
    api_kind_tokens: FrozenSet[str] = frozenset()
    markup_tokens: FrozenSet[Tuple[str, int]] = frozenset()
    front_matter_keys: FrozenSet[str] = frozenset()
    front_matter_values: FrozenSet[Tuple[str, str]] = frozenset()
    shortcode_values: FrozenSet[str] = frozenset()
    internal_links: FrozenSet[str] = frozenset()
    code_identifiers: FrozenSet[str] = frozenset()
    example_files: FrozenSet[str] = frozenset()


@dataclass
class FileStats:
    l10n_to_en_line_ratio: float
    l10n_to_en_body_word_ratio: float
    missing_h2: int
    missing_h3: int
    missing_code_blocks: int
    missing_anchors: int
    missing_new_versions: int
    extra_headings: int = 0
    heading_level_shift: bool = False
    missing_feature_state: int = 0
    missing_api_or_kind: int = 0
    markup_token_mismatches: Tuple[Tuple[str, int, int], ...] = ()
    missing_front_matter_keys: FrozenSet[str] = frozenset()
    missing_front_matter_values: FrozenSet[Tuple[str, str]] = frozenset()
    missing_shortcode_values: FrozenSet[str] = frozenset()
    missing_internal_links: FrozenSet[str] = frozenset()
    missing_code_identifiers: FrozenSet[str] = frozenset()
    outdated_local_examples: FrozenSet[str] = frozenset()

@dataclass
class FileReport:
    localized_path: str
    status: str
    reasons: List[str] = field(default_factory=list)
    indicators: List[str] = field(default_factory=list)
    is_minor_fix: bool = False

# --- Markdown parsing ---

def _is_indented_code_block(raw_para: str) -> bool:
    lines = raw_para.splitlines()
    non_blank = [line for line in lines if line.strip()]
    return bool(non_blank) and all(line[:4] == "    " for line in non_blank)

def _count_visible_lines(text: str) -> int:
    # Code-block contents kept: code volume is legitimate content.
    t = _STRIP_FM.sub("", text, count=1)
    t = _STRIP_CMNT.sub("", t)
    return sum(1 for line in t.splitlines() if line.strip())

_STRIP_CMNT_LINE = re.compile(r"<!--.*?-->[ \t]*\n?", re.DOTALL)

def _count_paragraphs(text: str) -> int:
    # Blank-line separated blocks outside front matter and HTML comments
    # (fenced code blocks collapse to a single block). Invariant to single-line
    # vs multi-line wrapping conventions across locales.
    t = _STRIP_FM.sub("", text, count=1)
    t = _STRIP_CMNT_LINE.sub("", t)
    t = _STRIP_CODE.sub("\n\nCODE_BLOCK\n\n", t)
    return sum(1 for p in re.split(r"\n[ \t]*\n+", t.strip()) if p.strip())

def _count_body_words(text: str) -> int:
    # For the Latin-compactness check: separates loose-wrapped full
    # translations from thinned content.
    t = _STRIP_FM.sub("", text, count=1)
    t = _STRIP_CMNT.sub("", t)
    t = _STRIP_CODE.sub("", t)
    kept: List[str] = []
    for raw in re.split(r"\n{2,}", t):
        if _is_indented_code_block(raw):
            continue
        kept.append(raw)
    t = _STRIP_INLINE.sub("", "\n\n".join(kept))
    return len(_BODY_WORD_RE.findall(t))

_FM_BLOCK_RE = re.compile(r"^\s*---\s*\n(.*?)\n---\s*(?:\n|$)", re.DOTALL)

def _extract_front_matter_keys(text: str) -> FrozenSet[str]:
    # Top-level keys only (column 0): nested keys like `card:\n  name:` would
    # otherwise collide across unrelated front-matter blocks. Commented-out
    # keys (`# reviewers:`) never match -- handled instead via
    # _OPTIONAL_FRONT_MATTER_KEYS at the comparison site.
    m = _FM_BLOCK_RE.match(text)
    if not m:
        return frozenset()
    return frozenset(_FM_KEY_RE.findall(m.group(1)))


def _normalize_internal_path(url: str, allow_bare_section: bool = False) -> str:
    """Normalize internal Kubernetes site paths (`/docs/...`, `/blog/...`, etc.)
    and official Kubernetes/CNCF external repo URLs (`github.com/kubernetes/...`,
    `k8s.io/...`, etc.) by stripping `https://kubernetes.io`, optional `/<locale>/`
    prefix (handled by Hugo's `render-link.html`), `#fragment`, `?query`, and
    trailing `/`."""
    url = url.strip().strip("\"'")
    if not url or url.startswith("#") or url.startswith("mailto:"):
        return ""
    url = re.sub(
        r"^https?://(?:(?:www\.)?kubernetes\.io|k8s\.io(?=/(?:docs|blog|community|releases|training|partners|case-studies|includes)(?:/|$)))/",
        "/",
        url,
    )
    if allow_bare_section and re.match(
        r"^(?:docs|blog|community|releases|training|partners|case-studies|includes)(?:/|$)",
        url,
    ):
        url = "/" + url
    clean_url = url.split("#")[0].split("?")[0].rstrip("/")
    clean_url = _URL_LOCALE_PREFIX_RE.sub(r"\1", clean_url)
    if (
        _K8S_OFFICIAL_EXTERNAL_URL_RE.match(clean_url)
        and "code-of-conduct-languages" not in clean_url
    ):
        return clean_url
    if not clean_url.startswith("/"):
        return ""
    if re.match(
        r"^/(?:docs|blog|community|releases|training|partners|case-studies|includes)(?:/|$)",
        clean_url,
    ):
        return clean_url
    return ""


def _extract_front_matter_values(text: str) -> FrozenSet[Tuple[str, str]]:
    """Extract structural front-matter key-value pairs using a Denylist so all
    non-prose scalar keys (current and future) and nested structural fields
    are compared between English and localized files."""
    m = _FM_BLOCK_RE.match(text)
    if not m:
        return frozenset()
    block = _STRIP_CMNT.sub("", m.group(1))
    pairs: Set[Tuple[str, str]] = set()
    for k, v in _FM_SCALAR_RE.findall(block):
        if k in _IGNORE_FRONT_MATTER_VALUE_KEYS:
            continue
        val = v.strip().strip("\"'")
        if not val or val in (">", ">-", "|", "|-"):
            continue
        if k in ("full_link", "full-link"):
            norm_val = _normalize_internal_path(val, allow_bare_section=True)
            val = norm_val or _URL_LOCALE_PREFIX_RE.sub(r"\1", val.rstrip("/"))
        elif val.lower() in ("true", "false"):
            val = val.lower()
        pairs.add((k, val))
    for nk, nv in _FM_NESTED_STRUCTURAL_RE.findall(block):
        if nk in ("apiVersion", "kind"):
            # Already tracked by `_extract_api_kind_tokens`.
            continue
        pairs.add((f"nested:{nk}", nv.strip().strip("\"'")))
    return frozenset(pairs)


def _extract_shortcode_values(text: str) -> FrozenSet[str]:
    """Extract non-translatable Hugo shortcode `key="value"` attributes and
    positional arguments outside front matter, comments, and fenced code."""
    body = _STRIP_CODE.sub(
        "", _STRIP_CMNT.sub("", _STRIP_FM.sub("", text, count=1))
    )
    tokens: Set[str] = set()
    for sm in _SHORTCODE_CALL_RE.finditer(body):
        name = sm.group(1).lstrip("-")
        if name.startswith("/") or name in ("feature_state", "feature-state"):
            continue
        args = sm.group(2).strip().rstrip("-").strip()
        kvs = _SHORTCODE_KV_RE.findall(args)
        if kvs:
            for ak, av in kvs:
                if ak in _TRANSLATABLE_SHORTCODE_ATTRS and not (
                    name == "feature-gate-description" and ak == "name"
                ):
                    continue
                val = av.strip()
                if ak == "term_id":
                    val = val.lower()
                elif ak in ("path", "url"):
                    val = _normalize_internal_path(val, allow_bare_section=True) or val
                tokens.add(f"{name}:{ak}={val}")
        elif args and name in _POSITIONAL_SHORTCODE_NAMES:
            val = args.strip().strip("\"'")
            if name in ("ref", "relref"):
                val = (
                    _normalize_internal_path(val, allow_bare_section=True)
                    or val.split("#")[0].rstrip("/")
                )
            elif name == "include":
                val = val.lstrip("/")
            tokens.add(f"{name}={val}")
        elif not args and name in _BARE_SHORTCODE_NAMES:
            tokens.add(name)
    return frozenset(tokens)


def _extract_internal_links(text: str) -> FrozenSet[str]:
    """Extract normalized internal site paths from inline and reference-style
    Markdown links outside front matter, comments, and code spans/blocks."""
    body = _STRIP_INLINE.sub(
        "",
        _STRIP_CODE.sub(
            "", _STRIP_CMNT.sub("", _STRIP_FM.sub("", text, count=1))
        ),
    )
    links: Set[str] = set()
    for lm in _MD_LINK_TARGET_RE.finditer(body):
        raw = lm.group(1) or lm.group(2) or ""
        norm = _normalize_internal_path(raw, allow_bare_section=True)
        if norm:
            links.add(norm)
    return frozenset(links)

def _count_markup_tokens(text: str) -> FrozenSet[Tuple[str, int]]:
    # Strip front matter, comments, and fenced code blocks first: zh-cn-style
    # `<!-- EN original -->` duplication would otherwise double every count,
    # and fenced code blocks (tracked separately via `missing_code_blocks`)
    # would dilute prose markup differences with identical code syntax.
    # Also strip inline `<code>...</code>` and Markdown inline code spans so
    # `<code>...</code>` vs `` `...` `` formatting does not skew `<`, `>`, `=`,
    # or `|` counts, normalize `<br/> - ` table bullets, and collapse the
    # second bracket pair of full reference links (`[text][ref]` -> `[text]`).
    t = _STRIP_FM.sub("", text, count=1)
    t = _STRIP_CMNT.sub("", t)
    t = _STRIP_CODE.sub("", t)
    t = _CODE_TAG_RE.sub("", t)
    t = _STRIP_INLINE.sub("", t)
    t_norm_bullets = _BR_BULLET_RE.sub("\n- ", t)
    t_norm_brackets = _REF_LINK_SECOND_BRACKET_RE.sub("]", t)
    # Strip Hugo shortcodes before counting `<`, `>`, `=` so shortcode
    # delimiters and `key="value"` attributes already compared by
    # `_extract_shortcode_values` are not double-counted as HTML/attribute
    # tokens, and strip self-contained inline shortcodes before counting
    # `{{` and `}}` so 1-2 tooltip/sample shortcode edits only fire
    # `shortcode_values` rather than `markup_token_mismatches`.
    t_no_sc = _SHORTCODE_CALL_RE.sub("", t)
    t_no_inline_sc = _TRACKED_INLINE_SHORTCODE_RE.sub("", t)
    counts: List[Tuple[str, int]] = []
    for tok in _MARKUP_TOKENS:
        if tok == "bullet_list":
            counts.append((tok, len(_BULLET_LIST_RE.findall(t_norm_bullets))))
        elif tok == "numbered_list":
            counts.append((tok, len(_NUMBERED_LIST_RE.findall(t))))
        elif tok in ("<", ">", "="):
            counts.append((tok, t_no_sc.count(tok)))
        elif tok in ("{{", "}}"):
            counts.append((tok, t_no_inline_sc.count(tok)))
        elif tok in ("[", "]"):
            counts.append((tok, t_norm_brackets.count(tok)))
        elif tok == "http":
            counts.append((tok, len(_HTTP_URL_RE.findall(t))))
        else:
            counts.append((tok, t.count(tok)))
    return frozenset(counts)

def _extract_structure(text: str) -> Tuple[int, int, int, int, FrozenSet[str]]:
    # Strip front matter and comments first: some localization teams add
    # comments, e.g., zh-cn uses `<!-- -->` blocks to record the English
    # original, which would desync `in_code`.
    # Toggle `in_code` on any fenced code block delimiter (including list-indented
    # fences where opening/closing indentation differs by 3 vs 4 spaces); only
    # count column-0 fences toward `code_blocks`.
    t = _STRIP_FM.sub("", text, count=1)
    lines = _STRIP_CMNT.sub("", t).splitlines()
    h2 = h3 = h4 = fences = 0
    anchors: set = set()
    in_code = False
    for line in lines:
        stripped = line.strip()
        leading = len(line) - len(line.lstrip(" "))
        if stripped.startswith("```"):
            if len(stripped) > 6 and stripped.endswith("```"):
                continue
            if leading == 0:
                fences += 1
            in_code = not in_code
            continue
        elif in_code and stripped.endswith("```"):
            if leading == 0:
                fences += 1
            in_code = False
            continue
        if in_code:
            continue
        if re.match(r"^####\s+\S", line):
            h4 += 1
        elif re.match(r"^###\s+\S", line):
            h3 += 1
        elif re.match(r"^##\s+\S", line):
            h2 += 1
        if line.startswith("#"):
            for m in _ANCHOR_RE.finditer(line):
                anchors.add(m.group(1).strip().lower())
    return h2, h3, h4, fences // 2, frozenset(anchors)

def _extract_feature_state_tokens(text: str) -> FrozenSet[str]:
    # Strip comments first: some localization teams add comments, e.g.,
    # zh-cn uses `<!-- -->` blocks to record the English original, which
    # would mask token drift.
    # Prefixes keep version/gate name spaces from colliding.
    no_cmt = _STRIP_CMNT.sub("", text)
    tokens = [f"version:{v}" for v in _FS_VERSION_RE.findall(no_cmt)]
    tokens.extend(f"gate:{g}" for g in _FS_GATE_RE.findall(no_cmt))
    tokens.extend(f"state:{s.lower()}" for s in _FS_STATE_RE.findall(no_cmt))
    m = _FM_BLOCK_RE.match(text)
    if m:
        for sm in _FG_STAGE_BLOCK_RE.finditer(m.group(1)):
            if sm.group(1):
                tokens.append(f"fg_stage:{sm.group(1).strip()}")
            else:
                tokens.append(f"fg_{sm.group(2)}:{sm.group(3).strip()}")
    return frozenset(tokens)

def _extract_api_kind_tokens(text: str) -> FrozenSet[str]:
    # Same comment-stripping rationale as feature_state. Prefixes keep
    # apiVersion, kind, and container image:tag value spaces separate.
    no_cmt = _STRIP_CMNT.sub("", text)
    tokens = [f"api:{v}" for v in _APIVERSION_LINE_RE.findall(no_cmt)]
    tokens.extend(f"kind:{k}" for k in _KIND_LINE_RE.findall(no_cmt))
    tokens.extend(f"image:{img}" for img in _IMAGE_TAG_LINE_RE.findall(no_cmt))
    return frozenset(tokens)


def _extract_code_identifiers(text: str) -> FrozenSet[str]:
    """Extract non-translatable CLI flags (`--flag`), CLI commands (`kubectl`,
    `kubeadm`, `dnf`, etc.), and kernel sysctl / `kubernetes.io/*` label keys
    inside fenced code blocks and inline code spans."""
    no_cmt = _STRIP_CMNT.sub("", _STRIP_FM.sub("", text, count=1))
    tokens: Set[str] = set()
    for cm in _CODE_SPAN_OR_BLOCK_RE.finditer(no_cmt):
        chunk = cm.group(0)
        for m in _CLI_FLAG_RE.finditer(chunk):
            tokens.add(f"flag:{m.group(1)}")
        for m in _CLI_CMD_RE.finditer(chunk):
            tokens.add(f"cmd:{' '.join(m.group(1).split())}")
        for m in _SYSCTL_OR_K8S_KEY_RE.finditer(chunk):
            tokens.add(f"key:{m.group(1)}")
    return frozenset(tokens)


def _extract_example_files(text: str) -> FrozenSet[str]:
    """Extract `file="..."` paths referenced by `code_sample`, `codenew`, or
    `code` shortcodes outside front matter, comments, and fenced code blocks."""
    body = _STRIP_CODE.sub(
        "", _STRIP_CMNT.sub("", _STRIP_FM.sub("", text, count=1))
    )
    return frozenset(
        m.group(1).strip().lstrip("/")
        for m in _EXAMPLE_SHORTCODE_FILE_RE.finditer(body)
        if m.group(1).strip()
    )


_EXAMPLE_NORM_CACHE: Dict[str, Optional[str]] = {}


def _get_normalized_example_code(path: str) -> Optional[str]:
    """Read and normalize an example file under `content/*/examples/`, stripping
    full-line/inline `#` comments and normalizing whitespace so translated
    comments or indentation differences do not trigger false alarms."""
    if path in _EXAMPLE_NORM_CACHE:
        return _EXAMPLE_NORM_CACHE[path]
    if not os.path.isfile(path):
        _EXAMPLE_NORM_CACHE[path] = None
        return None
    try:
        with open(path, encoding="utf-8-sig", errors="replace") as fh:
            raw = fh.read()
    except OSError:
        _EXAMPLE_NORM_CACHE[path] = None
        return None
    lines: List[str] = []
    for line in raw.splitlines():
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        s = re.sub(r"[ \t]+#.*$", "", s)
        s = re.sub(r"\s+", " ", s)
        lines.append(s)
    norm = "\n".join(lines)
    _EXAMPLE_NORM_CACHE[path] = norm
    return norm


def _find_outdated_local_examples(
    example_files: FrozenSet[str],
    en_path: str,
    l10n_path: str,
    locale: str,
) -> FrozenSet[str]:
    """Return example file paths referenced by `l10n` whose local copy under
    `content/<locale>/examples/` exists and differs in non-comment code from
    `content/en/examples/`."""
    if not example_files or "content/en/" not in en_path:
        return frozenset()
    en_prefix = en_path.split("content/en/")[0]
    l10n_marker = f"content/{locale}/"
    l10n_prefix = (
        l10n_path.split(l10n_marker)[0] if l10n_marker in l10n_path else en_prefix
    )
    en_ex_dir = os.path.join(en_prefix, "content", "en", "examples")
    l10n_ex_dir = os.path.join(l10n_prefix, "content", locale, "examples")
    outdated: Set[str] = set()
    for rel_ex in example_files:
        l10n_ex_path = os.path.join(l10n_ex_dir, rel_ex)
        l10n_norm = _get_normalized_example_code(l10n_ex_path)
        if l10n_norm is None:
            continue
        en_ex_path = os.path.join(en_ex_dir, rel_ex)
        en_norm = _get_normalized_example_code(en_ex_path)
        if en_norm is not None and l10n_norm != en_norm:
            outdated.add(rel_ex)
    return frozenset(outdated)


def parse_markdown(path: str, locale: str = "") -> ParsedFile:
    del locale
    with open(path, encoding="utf-8-sig", errors="replace") as fh:
        text = fh.read()
    is_l10n = "content/en/" not in path.replace("\\", "/")
    no_cmt = _STRIP_CMNT.sub("", text)
    if is_l10n:
        versions = frozenset(
            (int(m.group(1) or m.group(3)), int(m.group(2) or m.group(4)))
            for m in _L10N_VERSION_RE.finditer(no_cmt)
        )
    else:
        versions = frozenset(
            (int(major), int(minor)) for major, minor in _VERSION_RE.findall(no_cmt)
        )
    h2, h3, h4, code_blocks, anchors = _extract_structure(text)
    return ParsedFile(
        visible_lines=_count_visible_lines(text),
        h2=h2, h3=h3, h4=h4, code_blocks=code_blocks,
        anchors=anchors,
        versions=versions,
        body_words=_count_body_words(text),
        paragraphs=_count_paragraphs(text),
        feature_state_tokens=_extract_feature_state_tokens(text),
        api_kind_tokens=_extract_api_kind_tokens(text),
        markup_tokens=_count_markup_tokens(text),
        front_matter_keys=_extract_front_matter_keys(text),
        front_matter_values=_extract_front_matter_values(text),
        shortcode_values=_extract_shortcode_values(text),
        internal_links=_extract_internal_links(text),
        code_identifiers=_extract_code_identifiers(text),
        example_files=_extract_example_files(text),
    )

# --- File comparison / stats ---

def _count_missing_new_versions(
    en_versions: FrozenSet[Tuple[int, int]],
    l10n_versions: FrozenSet[Tuple[int, int]],
) -> int:
    if not l10n_versions:
        return len(en_versions)
    l10n_max = max(l10n_versions)
    return sum(1 for v in en_versions if v > l10n_max)

def _compute_markup_token_mismatches(
    en_tokens: FrozenSet[Tuple[str, int]], l10n_tokens: FrozenSet[Tuple[str, int]],
) -> Tuple[Tuple[str, int, int], ...]:
    en_map = dict(en_tokens)
    l10n_map = dict(l10n_tokens)
    mismatches = []
    for tok in _MARKUP_TOKENS:
        e, k = en_map.get(tok, 0), l10n_map.get(tok, 0)
        if e == 0 and k == 0:
            continue
        diff = e - k
        rel = abs(diff) / max(e, 1)
        if abs(diff) >= _TOKEN_MISMATCH_ABS_MIN and rel >= _TOKEN_MISMATCH_REL_MIN:
            mismatches.append((tok, e, k))
    return tuple(mismatches)

def compute_stats(
    en: ParsedFile,
    l10n: ParsedFile,
    outdated_local_examples: FrozenSet[str] = frozenset(),
) -> FileStats:
    line_ratio = (
        min(l10n.visible_lines / en.visible_lines, 2.0)
        if en.visible_lines > 0 else 1.0
    )
    body_word_ratio = (
        l10n.body_words / en.body_words if en.body_words > 0 else 1.0
    )

    if l10n.visible_lines > 0:
        missing_feature_state = len(en.feature_state_tokens ^ l10n.feature_state_tokens)
        missing_api_or_kind = len(en.api_kind_tokens - l10n.api_kind_tokens)
        missing_shortcode_values = en.shortcode_values - l10n.shortcode_values
        missing_internal_links = en.internal_links - l10n.internal_links
        missing_code_identifiers = en.code_identifiers - l10n.code_identifiers
        outdated_examples = outdated_local_examples
    else:
        missing_feature_state = 0
        missing_api_or_kind = 0
        missing_shortcode_values = frozenset()
        missing_internal_links = frozenset()
        missing_code_identifiers = frozenset()
        outdated_examples = frozenset()

    # Only report front-matter value mismatches for keys present in both files
    # (or nested structural keys whose parent block exists in localized), so a
    # missing key isn't double-counted in both `missing_front_matter_keys` and
    # `missing_front_matter_values`.
    _nested_parent = {
        "nested:list": "_build",
        "nested:render": "_build",
        "nested:import": "feature",
        "nested:major": "release_announcement",
        "nested:minor": "release_announcement",
        "nested:latest": "release_announcement",
        "nested:ReleaseType": "release_announcement",
    }
    missing_fm_values = frozenset(
        (k, v)
        for k, v in (en.front_matter_values - l10n.front_matter_values)
        if _nested_parent.get(k, k) in l10n.front_matter_keys
    )

    missing_h2 = max(0, en.h2 - l10n.h2)
    missing_h3 = max(0, en.h3 - l10n.h3)
    en_total_h = en.h2 + en.h3 + en.h4
    l10n_total_h = l10n.h2 + l10n.h3 + l10n.h4
    shifted_headings = max(
        abs(en.h2 - l10n.h2), abs(en.h3 - l10n.h3), abs(en.h4 - l10n.h4)
    )
    heading_level_shift = (
        l10n.visible_lines > 0
        and en_total_h == l10n_total_h
        and 1 <= (missing_h2 + missing_h3) <= 3
        and 1 <= shifted_headings <= 3
    )
    extra_headings = (
        max(0, l10n_total_h - en_total_h)
        if l10n.visible_lines > 0 and (l10n.h2 > en.h2 or l10n.h3 > en.h3)
        else 0
    )

    return FileStats(
        l10n_to_en_line_ratio=line_ratio,
        l10n_to_en_body_word_ratio=body_word_ratio,
        missing_h2=missing_h2,
        missing_h3=missing_h3,
        missing_code_blocks=max(0, en.code_blocks - l10n.code_blocks),
        missing_anchors=len(en.anchors - l10n.anchors),
        missing_new_versions=_count_missing_new_versions(en.versions, l10n.versions),
        extra_headings=extra_headings,
        heading_level_shift=heading_level_shift,
        missing_feature_state=missing_feature_state,
        missing_api_or_kind=missing_api_or_kind,
        markup_token_mismatches=_compute_markup_token_mismatches(
            en.markup_tokens, l10n.markup_tokens
        ),
        missing_front_matter_keys=(
            (en.front_matter_keys - l10n.front_matter_keys)
            - _OPTIONAL_FRONT_MATTER_KEYS
        ),
        missing_front_matter_values=missing_fm_values,
        missing_shortcode_values=missing_shortcode_values,
        missing_internal_links=missing_internal_links,
        missing_code_identifiers=missing_code_identifiers,
        outdated_local_examples=outdated_examples,
    )

# --- Length-gap classification ---

def _classify_length_gap(l10n_to_en_line_ratio: float) -> str:
    if l10n_to_en_line_ratio < 0.50:
        return _LENGTH_GAP_LARGE
    if l10n_to_en_line_ratio < 0.65:
        return _LENGTH_GAP_MODERATE
    if l10n_to_en_line_ratio < 0.80:
        return _LENGTH_GAP_SMALL
    if l10n_to_en_line_ratio < 0.90:
        return _LENGTH_GAP_SILENT
    return _LENGTH_GAP_NONE

def _build_length_gap_reason(level: str, l10n_to_en_line_ratio: float) -> str:
    ratio_str = (
        "<0.01"
        if 0 < l10n_to_en_line_ratio < 0.005
        else f"{l10n_to_en_line_ratio:.2f}"
    )
    if level == _LENGTH_GAP_LARGE:
        inv = (
            f"{1 / l10n_to_en_line_ratio:.1f}×"
            if l10n_to_en_line_ratio > 0 else "∞"
        )
        return f"{inv} shorter than EN (line ratio {ratio_str})"
    if level == _LENGTH_GAP_MODERATE:
        return f"substantially shorter than EN (line ratio {ratio_str})"
    if level == _LENGTH_GAP_SMALL:
        return f"moderately shorter than EN (line ratio {ratio_str})"
    return ""

def _is_only_length_gap(stats: FileStats) -> bool:
    # True when no structural loss is present — only a length gap fired.
    return (stats.missing_h2 == 0
            and stats.missing_h3 == 0
            and stats.missing_code_blocks == 0
            and stats.missing_anchors == 0
            and stats.missing_new_versions == 0)

def _should_ignore_length_gap(
    stats: FileStats, en: ParsedFile, l10n: ParsedFile,
    profile: LocaleProfile, level: str, has_support: bool,
) -> bool:
    """Drop length gap when unreliable (no corroborating structural loss or
    full body-word volume compared to English) or expected by locale shape.
    Profile-driven so adding a locale is a single map entry:
    `ignore_only_length_gap` handles locales such as Japanese where visible 
    line counts can differ from English because of Japanese wrapping behavior; 
    `compactness_guard` covers Latin-script locales whose full
    translations run loose-wrapped at high body-word ratios."""
    if level == _LENGTH_GAP_NONE or l10n.visible_lines == 0:
        return False
    if not has_support or stats.l10n_to_en_body_word_ratio >= _LATIN_BODY_RATIO_MIN:
        return True
    if (level in (_LENGTH_GAP_MODERATE, _LENGTH_GAP_LARGE)
            and _is_only_length_gap(stats)):
        if (profile.ignore_only_length_gap
                and en.visible_lines >= profile.short_en_threshold):
            return True
        if (profile.compactness_guard
                and en.visible_lines >= profile.compactness_min_en_lines
                and stats.l10n_to_en_body_word_ratio >= profile.body_word_ratio_min):
            return True
    return False

# --- Indicator detection ---

def _has_length_gap_support(stats: FileStats) -> bool:
    """Return whether non-length indicators support a length-gap finding."""
    return (
        stats.missing_h2 > 0
        or stats.missing_h3 > 0
        or stats.missing_code_blocks > 0
        or stats.missing_new_versions > 0
        or len(stats.markup_token_mismatches) >= 2
        or len(stats.missing_internal_links) >= _STRONG_INTERNAL_LINK_MISMATCH_THRESHOLD
    )


def _has_standalone_volume_loss(
    stats: FileStats, en: ParsedFile, l10n: ParsedFile, profile: LocaleProfile,
) -> bool:
    """Return True when a localized file has severe standalone volume/paragraph
    loss (e.g. pure-prose paragraphs added in EN or heavily abridged translation)
    even without structural token mismatches."""
    if l10n.visible_lines == 0:
        return False
    # Case 1: >=2 paragraphs missing and <=50% of EN paragraphs remain,
    # accompanied by reduced word volume. Paragraph count is invariant to
    # single-line vs multi-line wrapping conventions across locales.
    if (
        en.paragraphs >= 4
        and (en.paragraphs - l10n.paragraphs) >= 2
        and (l10n.paragraphs / en.paragraphs) <= 0.50
        and stats.l10n_to_en_body_word_ratio < _LATIN_BODY_RATIO_MIN
    ):
        return True
    # Case 2: Non-CJK/non-Indic locale with >=20 EN lines where both visible
    # line count (<50%) and word count (<60%) are less than half of EN.
    if (
        not profile.ignore_only_length_gap
        and en.visible_lines >= 20
        and stats.l10n_to_en_line_ratio < 0.50
        and stats.l10n_to_en_body_word_ratio < 0.60
    ):
        return True
    return False


def build_indicators(
    stats: FileStats, en: ParsedFile, l10n: ParsedFile, profile: LocaleProfile,
) -> List[str]:
    indicators: List[str] = []

    if l10n.visible_lines == 0 and en.visible_lines >= 1:
        indicators.append("empty_stub")

    # Empty-stub bypass on the short-EN floor so empty stubs still reach a level.
    if (en.visible_lines >= profile.min_en_lines_for_length_gap
            or l10n.visible_lines == 0):
        level = _classify_length_gap(stats.l10n_to_en_line_ratio)
    else:
        level = _LENGTH_GAP_NONE

    standalone_vol_loss = _has_standalone_volume_loss(stats, en, l10n, profile)
    has_support = _has_length_gap_support(stats) or standalone_vol_loss

    if standalone_vol_loss and level not in (_LENGTH_GAP_LARGE, _LENGTH_GAP_MODERATE):
        level = _LENGTH_GAP_MODERATE

    if not standalone_vol_loss and _should_ignore_length_gap(
        stats, en, l10n, profile, level, has_support
    ):
        level = _LENGTH_GAP_NONE

    if level == _LENGTH_GAP_LARGE and l10n.visible_lines > 0:
        indicators.append("large_length_gap")
    elif level == _LENGTH_GAP_MODERATE:
        indicators.append("moderate_length_gap")

    if (stats.missing_h2 >= _STRONG_H2_THRESHOLD
            or stats.extra_headings >= 3
            or (stats.missing_h2 >= 1 and stats.missing_h3 >= _STRONG_H3_WITH_H2_THRESHOLD)):
        indicators.append("severe_heading_loss")
    elif stats.missing_h2 >= 1 or stats.missing_h3 >= 1 or stats.extra_headings >= 1:
        indicators.append("moderate_heading_loss")

    if stats.missing_code_blocks >= _STRONG_CODE_THRESHOLD:
        indicators.append("severe_code_loss")
    elif stats.missing_code_blocks >= 1:
        indicators.append("moderate_code_loss")

    if stats.missing_anchors >= _STRONG_ANCHOR_THRESHOLD:
        indicators.append("severe_anchor_loss")
    elif stats.missing_anchors >= 1:
        indicators.append("moderate_anchor_loss")

    if stats.missing_new_versions >= _STRONG_VERSION_THRESHOLD:
        indicators.append("severe_version_mismatch")
    elif stats.missing_new_versions >= 1:
        indicators.append("moderate_version_mismatch")

    if stats.missing_feature_state and stats.missing_api_or_kind:
        indicators.append("severe_api_and_feature_mismatch")
    elif stats.missing_feature_state or stats.missing_api_or_kind:
        indicators.append("moderate_api_or_feature_mismatch")

    if len(stats.markup_token_mismatches) >= _STRONG_TOKEN_MISMATCH_THRESHOLD:
        indicators.append("severe_markup_token_loss")
    elif stats.markup_token_mismatches:
        indicators.append("moderate_markup_token_loss")

    if stats.missing_front_matter_keys:
        indicators.append("missing_front_matter_keys")

    if stats.missing_front_matter_values:
        indicators.append("front_matter_value_mismatch")

    if len(stats.missing_shortcode_values) >= _STRONG_SHORTCODE_MISMATCH_THRESHOLD:
        indicators.append("severe_shortcode_mismatch")
    elif stats.missing_shortcode_values:
        indicators.append("moderate_shortcode_mismatch")

    if len(stats.missing_internal_links) >= _STRONG_INTERNAL_LINK_MISMATCH_THRESHOLD:
        indicators.append("severe_internal_link_loss")
    elif stats.missing_internal_links:
        indicators.append("moderate_internal_link_loss")

    if len(stats.missing_code_identifiers) >= _STRONG_CODE_IDENTIFIER_MISMATCH_THRESHOLD:
        indicators.append("severe_code_identifier_mismatch")
    elif stats.missing_code_identifiers:
        indicators.append("moderate_code_identifier_mismatch")

    if len(stats.outdated_local_examples) >= _STRONG_SHORTCODE_MISMATCH_THRESHOLD:
        indicators.append("severe_example_file_mismatch")
    elif stats.outdated_local_examples:
        indicators.append("moderate_example_file_mismatch")

    return indicators

# --- Status classification ---

def _is_expected_translated_anchor_loss(
    non_length_gap_supporting: Set[str], profile: LocaleProfile,
    l10n_to_en_body_word_ratio: float, missing_anchors: int,
) -> bool:
    # Latin: some locales translate anchor IDs instead of preserving the
    # source identifier — looks compact with a small anchor mismatch but
    # carries full word volume. Without this guard, rule 4 falsely promotes them.
    return (
        profile.compactness_guard
        and l10n_to_en_body_word_ratio >= profile.body_word_ratio_min
        and missing_anchors <= 2
        and len(non_length_gap_supporting) >= 1
        and all(s == "moderate_anchor_loss" for s in non_length_gap_supporting)
    )

def classify_status(
    indicators: List[str], *,
    profile: LocaleProfile, l10n_to_en_body_word_ratio: float, missing_anchors: int,
) -> str:
    """Classification rules, in order:

    1. Any deterministic structural or token mismatch (`_STRONG_INDICATORS`)
       → `Strong signal` (subdivided into `Major fix` vs `Minor fix`).
    2. Heuristic/indirect signals (`_SUPPORTING_INDICATORS`: standalone
       length/paragraph gap, `moderate_markup_token_loss`, `moderate_anchor_loss`)
       → `Moderate signal` (requires manual verification).
    3. Otherwise → `No signal`.
    """
    if not indicators:
        return STATUS_NO_SIGNAL

    indset = set(indicators)
    if indset & _STRONG_INDICATORS:
        return STATUS_STRONG_SIGNAL
    if indset & _SUPPORTING_INDICATORS:
        return STATUS_MODERATE_SIGNAL
    return STATUS_NO_SIGNAL

# --- Reason generation ---

_ONLY_ANCHOR_INDICATOR_SUFFIX = " (only indicator — verify anchor naming)"

_FALLBACK_REASON = "content indicators suggest localized file may be outdated"

def build_reasons(
    stats: FileStats, en: ParsedFile, l10n: ParsedFile,
    locale: str, indicators: List[str],
) -> List[str]:
    reasons: List[str] = []
    indset = set(indicators)

    if "empty_stub" in indset:
        reasons.append(f"no visible body content (EN has {en.visible_lines} lines)")

    if "large_length_gap" in indset:
        r = _build_length_gap_reason(_LENGTH_GAP_LARGE, stats.l10n_to_en_line_ratio)
        if en.paragraphs >= 4 and (en.paragraphs - l10n.paragraphs) >= 2 and (l10n.paragraphs / en.paragraphs) <= 0.50:
            r += f"; missing {en.paragraphs - l10n.paragraphs} of {en.paragraphs} paragraphs"
        reasons.append(r)

    if stats.heading_level_shift:
        shifted = max(
            abs(en.h2 - l10n.h2), abs(en.h3 - l10n.h3), abs(en.h4 - l10n.h4)
        )
        reasons.append(
            f"heading level mismatch ({shifted} heading(s) shifted between H2/H3/H4)"
        )
    elif stats.missing_h2 > 0 or stats.missing_h3 > 0:
        parts = []
        if stats.missing_h2:
            parts.append(f"{stats.missing_h2} H2")
        if stats.missing_h3:
            parts.append(f"{stats.missing_h3} H3")
        reasons.append(f"missing headings ({', '.join(parts)})")
    elif stats.extra_headings > 0:
        reasons.append(
            f"extra headings in localized ({stats.extra_headings} section(s) removed in EN)"
        )

    if stats.missing_code_blocks:
        reasons.append(f"missing {stats.missing_code_blocks} code block(s)")

    only_anchor = len(indicators) == 1
    if stats.missing_anchors and (
        "severe_anchor_loss" in indset or only_anchor
    ):
        r = f"missing {stats.missing_anchors} section anchor(s)"
        if only_anchor:
            r += _ONLY_ANCHOR_INDICATOR_SUFFIX
        reasons.append(r)

    if stats.missing_new_versions:
        reasons.append(
            f"missing {stats.missing_new_versions} Kubernetes version reference(s)"
        )

    if stats.missing_feature_state and stats.missing_api_or_kind:
        reasons.append("missing feature-state and apiVersion/kind value(s)")
    elif stats.missing_feature_state:
        reasons.append(f"missing {stats.missing_feature_state} feature-state token(s)")
    elif stats.missing_api_or_kind:
        reasons.append(f"missing {stats.missing_api_or_kind} apiVersion/kind value(s)")

    # Emit severe semantic mismatches (shortcodes, local examples, links, CLI
    # identifiers) before moderate length/markup counts so `reasons[0]` in
    # `Major fix` always highlights the primary structural/semantic drift.
    semantic_reasons: List[Tuple[bool, str]] = []

    if stats.missing_shortcode_values:
        shown_sc = sorted(stats.missing_shortcode_values)[:5]
        parts = [f"`{s}`" for s in shown_sc]
        more = (
            f", +{len(stats.missing_shortcode_values) - 5} more"
            if len(stats.missing_shortcode_values) > 5 else ""
        )
        semantic_reasons.append((
            "severe_shortcode_mismatch" in indset,
            f"missing {len(stats.missing_shortcode_values)} shortcode value(s): "
            f"{', '.join(parts)}{more}",
        ))

    if stats.outdated_local_examples:
        shown_ex = sorted(stats.outdated_local_examples)[:5]
        parts = [f"`{ex}`" for ex in shown_ex]
        more = (
            f", +{len(stats.outdated_local_examples) - 5} more"
            if len(stats.outdated_local_examples) > 5 else ""
        )
        semantic_reasons.append((
            "severe_example_file_mismatch" in indset,
            f"outdated {len(stats.outdated_local_examples)} local example(s): "
            f"{', '.join(parts)}{more}",
        ))

    if stats.missing_internal_links:
        shown_lnk = sorted(stats.missing_internal_links)[:5]
        parts = [f"`{lnk}`" for lnk in shown_lnk]
        more = (
            f", +{len(stats.missing_internal_links) - 5} more"
            if len(stats.missing_internal_links) > 5 else ""
        )
        semantic_reasons.append((
            "severe_internal_link_loss" in indset,
            f"missing {len(stats.missing_internal_links)} link target(s): "
            f"{', '.join(parts)}{more}",
        ))

    if stats.missing_code_identifiers:
        shown_ci = sorted(stats.missing_code_identifiers)[:5]
        parts = [f"`{ci}`" for ci in shown_ci]
        more = (
            f", +{len(stats.missing_code_identifiers) - 5} more"
            if len(stats.missing_code_identifiers) > 5 else ""
        )
        semantic_reasons.append((
            "severe_code_identifier_mismatch" in indset,
            f"missing {len(stats.missing_code_identifiers)} CLI/code identifier(s): "
            f"{', '.join(parts)}{more}",
        ))

    for is_severe, text_r in semantic_reasons:
        if is_severe:
            reasons.append(text_r)

    if "moderate_length_gap" in indset:
        if (
            en.paragraphs >= 4
            and (en.paragraphs - l10n.paragraphs) >= 2
            and (l10n.paragraphs / en.paragraphs) <= 0.50
            and stats.l10n_to_en_line_ratio >= 0.65
        ):
            reasons.append(
                f"missing {en.paragraphs - l10n.paragraphs} of {en.paragraphs} paragraphs "
                f"(word ratio {stats.l10n_to_en_body_word_ratio:.2f})"
            )
        else:
            r = _build_length_gap_reason(_LENGTH_GAP_MODERATE, stats.l10n_to_en_line_ratio)
            if en.paragraphs >= 4 and (en.paragraphs - l10n.paragraphs) >= 2 and (l10n.paragraphs / en.paragraphs) <= 0.50:
                r += f"; missing {en.paragraphs - l10n.paragraphs} of {en.paragraphs} paragraphs"
            reasons.append(r)
    elif "small_length_gap" in indset:
        reasons.append(_build_length_gap_reason(_LENGTH_GAP_SMALL, stats.l10n_to_en_line_ratio))
    elif (
        abs(en.paragraphs - l10n.paragraphs) >= 5
        and abs(en.paragraphs - l10n.paragraphs) / max(en.paragraphs, 1) >= 0.25
    ):
        if en.paragraphs > l10n.paragraphs:
            reasons.append(
                f"missing {en.paragraphs - l10n.paragraphs} of {en.paragraphs} paragraphs"
            )
        else:
            reasons.append(
                f"extra {l10n.paragraphs - en.paragraphs} paragraphs in localized "
                f"(L10N {l10n.paragraphs} vs EN {en.paragraphs})"
            )

    if stats.markup_token_mismatches and "severe_markup_token_loss" in indset:
        shown = stats.markup_token_mismatches[:5]
        parts = [f"`{tok}` (EN {e} vs {k})" for tok, e, k in shown]
        more = (
            f", +{len(stats.markup_token_mismatches) - 5} more"
            if len(stats.markup_token_mismatches) > 5 else ""
        )
        reasons.append(f"markup count mismatch: {', '.join(parts)}{more}")

    for is_severe, text_r in semantic_reasons:
        if not is_severe:
            reasons.append(text_r)

    if stats.missing_anchors and not (
        "severe_anchor_loss" in indset or only_anchor
    ):
        reasons.append(f"missing {stats.missing_anchors} section anchor(s)")

    if stats.missing_front_matter_keys:
        keys = ", ".join(f"`{k}`" for k in sorted(stats.missing_front_matter_keys))
        reasons.append(f"missing front-matter key(s): {keys}")

    if stats.missing_front_matter_values:
        shown_fm = sorted(stats.missing_front_matter_values)[:5]
        parts = [f"`{k}={v}`" for k, v in shown_fm]
        more = (
            f", +{len(stats.missing_front_matter_values) - 5} more"
            if len(stats.missing_front_matter_values) > 5 else ""
        )
        reasons.append(f"front-matter value mismatch: {', '.join(parts)}{more}")

    if stats.markup_token_mismatches and "severe_markup_token_loss" not in indset:
        shown = stats.markup_token_mismatches[:5]
        parts = [f"`{tok}` (EN {e} vs {k})" for tok, e, k in shown]
        more = (
            f", +{len(stats.markup_token_mismatches) - 5} more"
            if len(stats.markup_token_mismatches) > 5 else ""
        )
        reasons.append(f"markup count mismatch: {', '.join(parts)}{more}")

    return reasons or [_FALLBACK_REASON]

# --- Git lastmod loading & per-file analysis ---

_GIT_LAST_COMMITS_CACHE: Dict[str, Dict[str, int]] = {}


def load_git_last_commits(repo_root: str) -> Dict[str, int]:
    """Return a map of repo-relative `content/...` paths to latest git commit
    Unix timestamps. Runs a single `git log` pass over `content/` and caches
    results per `repo_root`. Returns `{}` if git is unavailable or fails."""
    abs_root = os.path.abspath(repo_root)
    if abs_root in _GIT_LAST_COMMITS_CACHE:
        return _GIT_LAST_COMMITS_CACHE[abs_root]

    last_ts: Dict[str, int] = {}
    try:
        out = subprocess.check_output(
            [
                "git", "log", "--first-parent", "-m",
                "--format=COMMIT:%ct", "--name-only", "--", "content/",
            ],
            cwd=abs_root,
            text=True,
            stderr=subprocess.DEVNULL,
            errors="replace",
        )
        cur_ts = 0
        for line in out.splitlines():
            if line.startswith("COMMIT:"):
                cur_ts = int(line.split(":", 1)[1])
            elif line.startswith("content/") and line not in last_ts:
                last_ts[line] = cur_ts
    except (OSError, subprocess.SubprocessError, ValueError):
        last_ts = {}

    _GIT_LAST_COMMITS_CACHE[abs_root] = last_ts
    return last_ts


_ORPHAN_RESOLUTION_CACHE: Dict[
    str,
    Tuple[
        Dict[str, Tuple[str, Optional[str], str, str, Tuple[str, ...]]],
        Dict[str, str],
    ],
] = {}


def load_en_orphan_resolution(
    repo_root: str,
) -> Tuple[
    Dict[str, Tuple[str, Optional[str], str, str, Tuple[str, ...]]],
    Dict[str, str],
]:
    """Load English add/rename/delete git history (`git log -M60% --diff-filter=ARD`)
    and static URL redirects (`static/_redirects.base`) once per `repo_root` so
    orphan localized files can report where their English source moved, split,
    or when it was removed."""
    abs_root = os.path.abspath(repo_root)
    if abs_root in _ORPHAN_RESOLUTION_CACHE:
        return _ORPHAN_RESOLUTION_CACHE[abs_root]

    events: Dict[str, Tuple[str, Optional[str], str, str, Tuple[str, ...]]] = {}
    try:
        out = subprocess.check_output(
            [
                "git", "log", "-M60%", "--diff-filter=ARD",
                "--name-status", "--format=COMMIT:%cs|%s", "--", "content/en/",
            ],
            cwd=abs_root,
            text=True,
            stderr=subprocess.DEVNULL,
            errors="replace",
        )
        commits: List[Tuple[str, str, List[List[str]]]] = []
        cur_date, cur_subj = "", ""
        cur_rows: List[List[str]] = []
        for line in out.splitlines():
            if line.startswith("COMMIT:"):
                if cur_rows:
                    commits.append((cur_date, cur_subj, cur_rows))
                cur_date, _, cur_subj = line[7:].partition("|")
                cur_rows = []
            elif "\t" in line:
                cur_rows.append(line.split("\t"))
        if cur_rows:
            commits.append((cur_date, cur_subj, cur_rows))

        for cdate, csubj, rows in commits:
            added_md = [
                r[1] for r in rows
                if r[0] == "A" and r[1].endswith(".md") and "/docs/" in r[1]
            ]
            deleted_md = [
                r[1] for r in rows
                if r[0] == "D" and r[1].endswith(".md") and "/docs/" in r[1]
            ]
            co_added = (
                tuple(sorted(
                    added_md,
                    key=lambda p: ("/included/" in p, p.endswith("/_index.md"), p),
                ))
                if (1 <= len(added_md) <= 15 and len(deleted_md) <= 3)
                else ()
            )
            for parts in rows:
                st = parts[0]
                old_p = parts[1]
                if st.startswith("R"):
                    new_p = parts[2] if len(parts) > 2 else None
                    if old_p not in events or events[old_p][0] == "D":
                        events[old_p] = (st, new_p, cdate, csubj, ())
                elif st == "D" and old_p not in events:
                    events[old_p] = ("D", None, cdate, csubj, co_added)
    except (OSError, subprocess.SubprocessError):
        events = {}

    redirects: Dict[str, str] = {}
    for rel_fn in ("static/_redirects.base", "static/_redirects"):
        p = os.path.join(abs_root, rel_fn)
        if not os.path.isfile(p):
            continue
        try:
            with open(p, encoding="utf-8", errors="replace") as fh:
                for line in fh:
                    s = line.strip()
                    if not s or s.startswith("#"):
                        continue
                    cols = s.split()
                    if len(cols) >= 2:
                        redirects[cols[0].rstrip("/")] = cols[1]
        except OSError:
            pass

    _ORPHAN_RESOLUTION_CACHE[abs_root] = (events, redirects)
    return events, redirects


def describe_orphan(rel_l10n: str, locale: str, repo_root: str) -> str:
    """Return a concise explanation of what happened to the English counterpart
    of an orphan localized file (renamed/moved, split into multiple files,
    redirected/merged, removed, or never existed in English)."""
    abs_root = os.path.abspath(repo_root)
    events, redirects = load_en_orphan_resolution(abs_root)
    rel_doc = rel_l10n.split(f"content/{locale}/", 1)[-1]
    en_p = f"content/en/{rel_doc}"
    url_path = "/" + re.sub(r"(/_index\.md|\.md)$", "", rel_doc).rstrip("/")
    redir = redirects.get(url_path)
    ev = events.get(en_p)
    cdate = ev[2] if ev else ""
    csubj = ev[3] if ev else ""
    co_added = ev[4] if ev else ()

    if ev and ev[1]:
        new_p: Optional[str] = ev[1]
        seen = {en_p}
        while (
            new_p
            and not os.path.isfile(os.path.join(abs_root, new_p))
            and new_p in events
            and new_p not in seen
        ):
            seen.add(new_p)
            if events[new_p][1]:
                new_p = events[new_p][1]
                cdate = events[new_p][2]
            else:
                break
        if new_p and os.path.isfile(os.path.join(abs_root, new_p)):
            return f"moved in EN to `{new_p}` ({cdate})"

    if redir and "#" not in redir:
        clean_r = redir.strip("/")
        cand_md = f"content/en/{clean_r}.md"
        if os.path.isfile(os.path.join(abs_root, cand_md)):
            date_sfx = f" ({cdate})" if cdate else ""
            return f"moved in EN to `{cand_md}`{date_sfx}"

    if len(co_added) >= 2:
        shown = [f"`{p}`" for p in co_added[:3]]
        more = f", +{len(co_added) - 3} more" if len(co_added) > 3 else ""
        return f"split in EN into {len(co_added)} files ({cdate}): {', '.join(shown)}{more}"

    if len(co_added) == 1 and os.path.isfile(os.path.join(abs_root, co_added[0])):
        return f"moved in EN to `{co_added[0]}` ({cdate})"

    if redir:
        if cdate:
            return f"removed in EN ({cdate}); redirects to `{redir}`"
        return f"redirects in EN to `{redir}`"

    if ev:
        return f"removed in EN ({cdate}: {csubj})"

    return "no EN git history found (verify filename or locale-specific page)"


_MAJOR_FIX_INDICATORS: FrozenSet[str] = frozenset({
    "empty_stub",
    "large_length_gap", "moderate_length_gap",
    "severe_heading_loss", "moderate_heading_loss",
    "severe_code_loss", "moderate_code_loss",
    "severe_markup_token_loss",
})
_MINOR_FIX_MAX_ITEMS = 4


def _is_minor_fix(
    stats: FileStats, en: ParsedFile, l10n: ParsedFile, indicators: List[str],
) -> bool:
    """Return True when body structure (headings, code blocks, line length,
    paragraphs, list/table structure) is intact and only 1..4
    metadata/reference/identifier items differ; otherwise return False
    (indicating `Major fix`)."""
    if not indicators:
        return False
    indset = set(indicators)
    major_inds = indset & _MAJOR_FIX_INDICATORS
    if stats.heading_level_shift:
        major_inds = major_inds - {"moderate_heading_loss", "severe_heading_loss"}
    if major_inds or stats.extra_headings > 0:
        return False
    if (
        abs(en.paragraphs - l10n.paragraphs) >= 5
        and abs(en.paragraphs - l10n.paragraphs) / max(en.paragraphs, 1) >= 0.25
    ):
        return False
    # Treat list/table structure drift (>=4 bullet/numbered items or table pipes)
    # as Major fix even when fewer than 4 token types mismatched overall.
    for tok, e, k in stats.markup_token_mismatches:
        if tok in ("bullet_list", "numbered_list", "|") and abs(e - k) >= 4:
            return False
    extra_examples = sum(
        1
        for ex in stats.outdated_local_examples
        if f"code_sample:file={ex}" not in stats.missing_shortcode_values
    )
    total = (
        len(stats.missing_front_matter_keys)
        + len(stats.missing_front_matter_values)
        + len(stats.missing_internal_links)
        + len(stats.missing_shortcode_values)
        + len(stats.missing_code_identifiers)
        + extra_examples
        + stats.missing_feature_state
        + stats.missing_api_or_kind
        + stats.missing_new_versions
        + stats.missing_anchors
        + (1 if stats.heading_level_shift else 0)
    )
    return 0 < total <= _MINOR_FIX_MAX_ITEMS


def analyze_file_pair(
    en_path: str,
    l10n_path: str,
    locale: str,
    en_lastmod: int = 0,
    l10n_lastmod: int = 0,
) -> FileReport:
    profile = get_locale_profile(locale)
    en = parse_markdown(en_path)
    l10n = parse_markdown(l10n_path)
    outdated_examples = _find_outdated_local_examples(
        l10n.example_files, en_path, l10n_path, locale
    )
    stats = compute_stats(en, l10n, outdated_local_examples=outdated_examples)
    indicators = build_indicators(stats, en, l10n, profile)
    status = classify_status(
        indicators,
        profile=profile,
        l10n_to_en_body_word_ratio=stats.l10n_to_en_body_word_ratio,
        missing_anchors=stats.missing_anchors,
    )
    is_minor_fix = False
    if status != STATUS_NO_SIGNAL:
        reasons = build_reasons(stats, en, l10n, locale, indicators)
        is_minor_fix = _is_minor_fix(stats, en, l10n, indicators)
    elif en_lastmod > l10n_lastmod > 0:
        status = STATUS_LASTMOD_ONLY
        en_date = datetime.date.fromtimestamp(en_lastmod).isoformat()
        l10n_date = datetime.date.fromtimestamp(l10n_lastmod).isoformat()
        indicators = ["lastmod_only"]
        reasons = [f"newer EN commit (EN {en_date} > {locale} {l10n_date})"]
    else:
        reasons = []
    return FileReport(
        localized_path=l10n_path,
        status=status,
        reasons=reasons,
        indicators=indicators,
        is_minor_fix=is_minor_fix,
    )

# --- Locale scanning ---

# Scope is intentionally `docs/` only. (Aside: ko/de/es flatten blog posts
# into `_posts/YYYY-MM-DD-slug` while EN/ja/zh-cn nest them as
# `_posts/YYYY/slug`, so the naive substitution below never matches blog
# posts in those locales and they're silently skipped -- known, deferred.)

def _is_candidate_orphan(l10n_path: str, locale: str) -> bool:
    fname = os.path.basename(l10n_path)
    if fname in _ORPHAN_SKIP_BASENAMES:
        return False
    # Locale-specific contribution/localization guides (e.g. localization_ko.md,
    # localization-de.md, localization_fr.md, localization_pt-br.md) have no
    # matching English file by design.
    if fname.startswith("localization_") or fname.startswith("localization-"):
        return False
    rel = l10n_path.split(f"content/{locale}/", 1)[-1]
    return rel.startswith("docs/")

def scan_locale(
    locale: str, repo_root: str,
) -> Tuple[List[FileReport], List[str]]:
    locale_dir = os.path.join(repo_root, "content", locale)
    if not os.path.isdir(locale_dir):
        print(f"error: locale directory not found: {locale_dir}", file=sys.stderr)
        sys.exit(1)

    last_commits = load_git_last_commits(repo_root)

    pairs: List[Tuple[str, str]] = []
    orphan_paths: List[str] = []
    for root, _, files in os.walk(locale_dir):
        for fname in sorted(files):
            if not fname.endswith(".md"):
                continue
            l10n_path = os.path.join(root, fname)
            en_path = re.sub(rf"content/{re.escape(locale)}/", "content/en/", l10n_path)
            if os.path.exists(en_path):
                pairs.append((en_path, l10n_path))
            elif _is_candidate_orphan(l10n_path, locale):
                orphan_paths.append(l10n_path)

    reports: List[FileReport] = []

    total = len(pairs)
    if total:
        print(f"  [{locale}] evaluating {total} file pairs ...", file=sys.stderr)
    for i, (en_path, l10n_path) in enumerate(pairs, 1):
        if i % 100 == 0:
            print(f"  [{locale}] {i}/{total}", file=sys.stderr)
        rel_en = _to_rel_path(en_path, repo_root)
        rel_l10n = _to_rel_path(l10n_path, repo_root)
        reports.append(
            analyze_file_pair(
                en_path,
                l10n_path,
                locale,
                en_lastmod=last_commits.get(rel_en, 0),
                l10n_lastmod=last_commits.get(rel_l10n, 0),
            )
        )

    reports.sort(
        key=lambda fr: (_STATUS_SORT_KEY[fr.status], fr.localized_path)
    )
    orphan_paths.sort()
    return reports, orphan_paths

# --- Report formatting ---

_GITHUB_BASE = "https://github.com/kubernetes/website/blob"

def build_file_links(
    rel_path: str, locale: str, link_mode: str,
    branch: str, output_dir: str, repo_root: str,
    locale_first: bool = False,
) -> str:
    """Build the "[(en)] [(locale)]" link pair shown after each file entry.
    `local` mode emits report-relative paths; otherwise GitHub blob URLs.
    `locale_first=True` swaps order for orphan entries."""
    en_rel = re.sub(rf"^content/{re.escape(locale)}/", "content/en/", rel_path)
    if link_mode == "local":
        en_target = os.path.relpath(os.path.join(repo_root, en_rel), output_dir)
        loc_target = os.path.relpath(os.path.join(repo_root, rel_path), output_dir)
    else:
        base = f"{_GITHUB_BASE}/{branch}"
        en_target = f"{base}/{en_rel}?plain=1"
        loc_target = f"{base}/{rel_path}?plain=1"
    en_link = f"[(en)]({en_target})"
    loc_link = f"[({locale})]({loc_target})"
    pair = f"{loc_link} {en_link}" if locale_first else f"{en_link} {loc_link}"
    return f"  {pair}"

def _to_rel_path(path: str, repo_root: str) -> str:
    try:
        return os.path.relpath(path, repo_root)
    except ValueError:
        return path

def _extract_doc_area(path: str, locale: str) -> str:
    m = re.search(rf"content/{re.escape(locale)}/([^/]+(?:/[^/]+)?)", path)
    if not m:
        return "(other)/"
    seg = m.group(1)
    if "." in seg.split("/")[-1]:
        seg = "/".join(seg.split("/")[:-1])
    return seg.rstrip("/") + "/"

def count_files_by_status(
    evaluated: List[FileReport],
) -> Tuple[int, int, int, int]:
    c = Counter(fr.status for fr in evaluated)
    return (
        c[STATUS_STRONG_SIGNAL],
        c[STATUS_MODERATE_SIGNAL],
        c[STATUS_LASTMOD_ONLY],
        c[STATUS_NO_SIGNAL],
    )

def _build_locale_profile_note(profile: LocaleProfile) -> List[str]:
    if not profile.notes:
        return []
    return [
        "**Locale-specific calibration note:**",
        "",
        f"> {profile.notes}",
        "",
    ]


def _build_report_disclaimer() -> List[str]:
    """Triage disclaimer + status-meaning block included in every report."""
    return [
        "> This report is a signal-based triage aid, not a final localization review.",
        "> It checks page structure and deterministic tokens such as headings, code blocks,",
        "> paragraphs, anchors, Kubernetes versions, API / feature-state / image values,",
        "> front-matter keys and values, shortcode attributes, internal/official links,",
        "> CLI/code identifiers, and local example files. It does not check translation",
        "> meaning or quality. Please manually verify flagged files.",
        "",
        "**Triage category meanings:**",
        "",
        "- `Orphan`: no matching English source; reports whether the English page was moved, split, redirected, or removed in git history.",
        "- `Strong signal`: deterministic structural or token mismatch found; likely needs update.",
        "  - `Major fix`: body structure/volume changed (headings, code blocks, paragraphs, list/table structure) or ≥5 token items differ.",
        "  - `Minor fix`: body structure intact; 1–4 metadata, link, shortcode, anchor, or CLI/API/version items differ.",
        "- `Moderate signal`: heuristic/indirect signal only (standalone volume/paragraph gap, 1–3 markup count differences, or 1–2 missing anchors); verify manually.",
        f"- `{STATUS_LASTMOD_ONLY}`: English source has a newer git commit timestamp (`lastmod`), with no structural or token signal found (e.g., typo or prose-only edits); verifying and updating is still recommended to clear the outdated notice on `kubernetes.io`.",
        "- `No signal`: no outdatedness signal found; lowest priority, not a guarantee that the translation is current.",
        "",
    ]

def _render_report_items(
    items: List[FileReport],
    locale: str,
    repo_root: str,
    detailed: bool,
    link_mode: Optional[str],
    branch: str,
    output_dir: str,
) -> List[str]:
    out: List[str] = []
    for fr in items:
        path = _to_rel_path(fr.localized_path, repo_root)
        links = (
            "\n" + build_file_links(path, locale, link_mode, branch, output_dir, repo_root)
            if link_mode else ""
        )
        if detailed and fr.reasons:
            out.append(f"**`{path}`**{links}")
            out.extend(f"- {r}" for r in fr.reasons)
            if fr.indicators:
                out.append(f"- Indicators: {', '.join(fr.indicators)}")
            out.append("")
        else:
            if (
                fr.is_minor_fix
                or fr.status == STATUS_MODERATE_SIGNAL
                or not (set(fr.indicators) & _MAJOR_FIX_INDICATORS)
            ) and len(fr.reasons) > 1:
                display_reasons = [
                    r for r in fr.reasons
                    if not (fr.is_minor_fix and r.startswith("markup count mismatch:"))
                ] or fr.reasons
                summary_reason = "; ".join(display_reasons)
            elif len(fr.reasons) > 1 and not (
                set(fr.indicators)
                & {
                    "empty_stub",
                    "large_length_gap",
                    "severe_heading_loss",
                    "moderate_heading_loss",
                    "severe_code_loss",
                    "moderate_code_loss",
                }
            ):
                summary_reason = "; ".join(fr.reasons[:3])
            else:
                summary_reason = fr.reasons[0] if fr.reasons else "(no indicators)"
            out.append(f"- `{path}` — {summary_reason}{links}")
    if items and not detailed:
        out.append("")
    return out


def build_locale_report(
    locale: str,
    evaluated: List[FileReport],
    orphans: List[str],
    repo_root: str,
    date: str,
    detailed: bool,
    link_mode: Optional[str] = None,
    branch: str = "main",
    output_dir: str = ".",
) -> str:
    profile = get_locale_profile(locale)
    strong, moderate, lastmod_only, no_signal = count_files_by_status(evaluated)
    total = len(evaluated) + len(orphans)

    by_status: Dict[str, List[FileReport]] = {
        STATUS_STRONG_SIGNAL: [],
        STATUS_MODERATE_SIGNAL: [],
        STATUS_LASTMOD_ONLY: [],
        STATUS_NO_SIGNAL: [],
    }
    for fr in evaluated:
        by_status[fr.status].append(fr)

    major_count = sum(1 for fr in by_status[STATUS_STRONG_SIGNAL] if not fr.is_minor_fix)
    minor_count = sum(1 for fr in by_status[STATUS_STRONG_SIGNAL] if fr.is_minor_fix)

    w = max(len(STATUS_STRONG_SIGNAL), len(STATUS_MODERATE_SIGNAL),
            len(STATUS_LASTMOD_ONLY), len(STATUS_NO_SIGNAL),
            len("Evaluated"), len("Orphan"), len("↳ Major fix"), len("↳ Minor fix"))
    lines: List[str] = [
        f"## Localization triage: `{locale}`",
        "",
        f"Generated: {date}  ",
        "Method: checks page structure and outdatedness indicators  ",
        "Script: `l10n-outdatedness-triage.py`",
        "",
    ]
    lines.extend(_build_report_disclaimer())
    lines.extend(_build_locale_profile_note(profile))
    lines.extend([
        "| Triage category | Count |",
        "|---|---:|",
        f"| {'Evaluated':<{w}} | {total} |",
        f"| {'Orphan':<{w}} | {len(orphans)} |",
        f"| {STATUS_STRONG_SIGNAL:<{w}} | {strong} |",
        f"| {'↳ Major fix':<{w}} | {major_count} |",
        f"| {'↳ Minor fix':<{w}} | {minor_count} |",
        f"| {STATUS_MODERATE_SIGNAL:<{w}} | {moderate} |",
        f"| {STATUS_LASTMOD_ONLY:<{w}} | {lastmod_only} |",
        f"| {STATUS_NO_SIGNAL:<{w}} | {no_signal} |",
        "",
    ])

    area_counts: Counter = Counter(
        _extract_doc_area(fr.localized_path, locale)
        for fr in evaluated
        if fr.status in (STATUS_STRONG_SIGNAL, STATUS_MODERATE_SIGNAL)
    )
    if area_counts:
        lines.extend(["**Top affected areas (flagged files):**", ""])
        for area, count in area_counts.most_common(8):
            lines.append(f"- `{area}`: {count} files")
        lines.append("")

    lines.extend([
        f"### Orphan localized files, no English source ({len(orphans)})",
        "",
    ])
    if orphans:
        lines.append(f"_{_ORPHAN_REASON}_")
        lines.append("")
        for path in orphans:
            rel = _to_rel_path(path, repo_root)
            note = describe_orphan(rel, locale, repo_root)
            links = "\n" + build_file_links(rel, locale, link_mode, branch, output_dir, repo_root, locale_first=True) if link_mode else ""
            lines.append(f"- `{rel}` — {note}{links}")
        lines.append("")
    else:
        lines.extend(["_None_", ""])

    for key in (STATUS_STRONG_SIGNAL, STATUS_MODERATE_SIGNAL, STATUS_LASTMOD_ONLY):
        items = by_status[key]
        lines.extend([f"### {key} ({len(items)})", ""])
        if key == STATUS_LASTMOD_ONLY and items:
            lines.extend([f"_{_LASTMOD_ONLY_NOTE}_", ""])
        if not items:
            lines.extend(["_None_", ""])
            continue
        if key == STATUS_STRONG_SIGNAL:
            major_items = [fr for fr in items if not fr.is_minor_fix]
            minor_items = [fr for fr in items if fr.is_minor_fix]
            lines.extend([f"#### Major fix ({len(major_items)})", ""])
            if major_items:
                lines.extend(_render_report_items(
                    major_items, locale, repo_root, detailed,
                    link_mode, branch, output_dir,
                ))
            else:
                lines.extend(["_None_", ""])
            lines.extend([f"#### Minor fix ({len(minor_items)})", ""])
            if minor_items:
                lines.extend(_render_report_items(
                    minor_items, locale, repo_root, detailed,
                    link_mode, branch, output_dir,
                ))
            else:
                lines.extend(["_None_", ""])
        else:
            lines.extend(_render_report_items(
                items, locale, repo_root, detailed,
                link_mode, branch, output_dir,
            ))

    return "\n".join(lines)

def build_index_report(
    results: List[Tuple[str, List[FileReport], List[str]]], date: str,
) -> str:
    lines = [
        "## Localization triage index",
        "",
        f"Generated: {date}  ",
        "Method: checks page structure and outdatedness indicators  ",
        "Script: `l10n-outdatedness-triage.py`",
        "",
    ]
    lines.extend(_build_report_disclaimer())
    lines.extend([
        f"| Locale | Report | Evaluated | Orphan | {STATUS_STRONG_SIGNAL} | ↳ Major fix | ↳ Minor fix | {STATUS_MODERATE_SIGNAL} | {STATUS_LASTMOD_ONLY} | {STATUS_NO_SIGNAL} |",
        "|---|---|---:|---:|---:|---:|---:|---:|---:|---:|",
    ])
    for locale, evaluated, orphans in results:
        strong, moderate, lastmod_only, no_signal = count_files_by_status(evaluated)
        major_count = sum(
            1 for fr in evaluated
            if fr.status == STATUS_STRONG_SIGNAL and not fr.is_minor_fix
        )
        minor_count = sum(
            1 for fr in evaluated
            if fr.status == STATUS_STRONG_SIGNAL and fr.is_minor_fix
        )
        total = len(evaluated) + len(orphans)
        fname = f"l10n-status-{locale}.md"
        lines.append(
            f"| `{locale}` | [{fname}]({fname}) | {total} |"
            f" {len(orphans)} | {strong} | {major_count} | {minor_count} |"
            f" {moderate} | {lastmod_only} | {no_signal} |"
        )
    lines.append("")
    return "\n".join(lines)

# --- CLI / orchestration ---

def _auto_detect_repo_root() -> Optional[str]:
    d = os.path.abspath(os.getcwd())
    while True:
        if os.path.isdir(os.path.join(d, "content", "en")):
            return d
        parent = os.path.dirname(d)
        if parent == d:
            return None
        d = parent

def _resolve_locales(args: argparse.Namespace, repo_root: str) -> List[str]:
    if args.lang:
        return args.lang
    content_dir = os.path.join(repo_root, "content")
    return sorted(
        d for d in os.listdir(content_dir)
        if os.path.isdir(os.path.join(content_dir, d)) and d != "en"
    )

def _build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Localization outdatedness triage helper. Classifies "
            "localized files by status using page structure and outdatedness indicators "
            "and emits compact reports; orphan localized docs are "
            "listed in a separate section."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    group = parser.add_mutually_exclusive_group(required=False)
    group.add_argument(
        "--lang", metavar="CODE", nargs="+",
        help="One or more locales to scan (e.g. --lang ko  or  --lang ko zh-cn ja)",
    )
    group.add_argument(
        "--all", action="store_true",
        help="Scan all locales under content/ except en (default when no option given)",
    )
    parser.add_argument(
        "--repo-root", default=None, metavar="DIR",
        help=(
            "Path to kubernetes/website repo root (auto-detected if omitted). "
            "Accepts relative paths, e.g. --repo-root ../website"
        ),
    )
    parser.add_argument(
        "--output-dir", "-o", default=".", metavar="DIR",
        help="Directory for report files (default: current directory)",
    )
    parser.add_argument(
        "--verbose", "-v", action="store_true",
        help="Show all indicator lines per file (default: one compact line)",
    )
    parser.add_argument(
        "--link", default=None, metavar="MODE", choices=["web", "local"],
        help=(
            "Add [(en)] and [(<locale>)] links after each file entry. "
            "MODE: 'web' for GitHub URLs (opens code view); "
            "'local' for paths relative to the output directory."
        ),
    )
    parser.add_argument(
        "--branch", default="main", metavar="BRANCH",
        help="Branch for GitHub links (default: main)",
    )
    return parser

def main() -> None:
    args = _build_arg_parser().parse_args()

    if args.repo_root:
        repo_root = os.path.abspath(args.repo_root)
    else:
        repo_root = _auto_detect_repo_root()
        if repo_root is None:
            print(
                "error: could not auto-detect repo root (no content/en found "
                "above cwd). Use --repo-root to specify it explicitly.",
                file=sys.stderr,
            )
            sys.exit(1)

    date = datetime.date.today().isoformat()
    locales = _resolve_locales(args, repo_root)
    os.makedirs(args.output_dir, exist_ok=True)
    abs_output_dir = os.path.abspath(args.output_dir)

    all_results: List[Tuple[str, List[FileReport], List[str]]] = []
    for locale in locales:
        print(f"Scanning content/{locale}/ ...", file=sys.stderr)
        evaluated, orphans = scan_locale(locale, repo_root)
        all_results.append((locale, evaluated, orphans))
        out_path = os.path.join(
            args.output_dir, f"l10n-status-{locale}.md"
        )
        with open(out_path, "w", encoding="utf-8") as fh:
            fh.write(build_locale_report(
                locale, evaluated, orphans, repo_root, date, args.verbose,
                link_mode=args.link, branch=args.branch,
                output_dir=abs_output_dir,
            ))
        strong, moderate, lastmod_only, no_signal = count_files_by_status(evaluated)
        print(
            f"Wrote {out_path}  "
            f"({len(orphans)} orphans, {strong} {STATUS_STRONG_SIGNAL}, "
            f"{moderate} {STATUS_MODERATE_SIGNAL}, "
            f"{lastmod_only} {STATUS_LASTMOD_ONLY}, {no_signal} {STATUS_NO_SIGNAL})",
            file=sys.stderr,
        )

    if len(locales) > 1:
        index_path = os.path.join(args.output_dir, "l10n-status-all.md")
        with open(index_path, "w", encoding="utf-8") as fh:
            fh.write(build_index_report(all_results, date))
        print(f"Wrote {index_path}", file=sys.stderr)

if __name__ == "__main__":
    main()
