# Shared Lean-source scanning primitives — SOURCED by scripts/ci and
# scripts/comparator-judge. Extracted 2026-08-02 (comparator-judge pre-merge
# audit): the judge wrapper had re-implemented the import matcher with the
# exact fail-open '^import ' anchor scripts/ci was hardened away from — the
# canonical definitions live HERE, once, so a gate cannot drift from them.

# Whitespace-, `public`- and `meta`-tolerant import matcher (audit response
# 2026-08-01; `meta` slot added at the 2026-08-02 delta-review): Lean
# accepts leading whitespace before `import`, extra whitespace after it,
# and — under the 4.31 module system — `public import`, `meta import` and
# `public meta import` (the form iris-lean itself uses; requires a `module`
# header, which no golean file has yet — the slot closes the hole before
# the first module-system opt-in can open it). All were invisible to a bare
# '^import ' anchor. Matched lines are normalized to canonical 'import X'
# before any allowlist check, so odd formatting is judged, never skipped.
IMPORT_RE='^[[:space:]]*(public[[:space:]]+)?(meta[[:space:]]+)?import[[:space:]]+'

# Strip Lean comments before extracting CLOSURE EDGES (delta-audit
# 2026-08-01): at a closure walk a match is evidence of a BUILD EDGE, so an
# import line quoted in a /- -/ block or docstring injects a phantom edge —
# fail-OPEN. Depth-counting handles nested block comments; `--` line
# comments truncate at depth 0. Allowlist/lint sites may keep the raw
# tolerant match: over-matching there only over-FLAGS (fail-closed).
strip_lean_comments() {
  awk '{
    line=$0; out=""; i=1
    while (i <= length(line)) {
      two = substr(line, i, 2)
      if (two == "/-") { d++; i += 2; continue }
      if (two == "-/" && d > 0) { d--; i += 2; continue }
      if (d == 0) {
        if (two == "--") break
        out = out substr(line, i, 1)
      }
      i++
    }
    print out
  }'
}

# Canonical extraction of a file's import list: comment-stripped, tolerant
# match, normalized to bare module names. THE only sanctioned way for a
# gate to read Lean imports as build edges.
lean_imports() {
  strip_lean_comments < "$1" | grep -E "$IMPORT_RE" | sed -E "s/$IMPORT_RE//" \
    | sed -E 's/[[:space:]]+$//'
}
