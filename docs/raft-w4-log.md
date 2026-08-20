# Raft W4.0 campaign log — the export unblock

Lane: `raft-w4` (worktree `.claude/worktrees/raft-w4`), supervised arc under
the standing merge/audit protocol. Charter: harness design
(`docs/2026-08-20_machine-twin-harness-design.md`) §8's W4.0 slice — the two
measured export blockers (H-9, H-10) plus H-11's package-level-var quarantine —
then the post-W4.0 census. Owns frontend, `Corpus/`, `baselines/`,
`raftsubject/`, `tools/raftsubject/`, and this log.

Base: `main` @ `422e9aa3`. Predecessor: `docs/raft-w3-log.md` (the gap census
this slice consumes: H-9/G-2/G-3 rows). `deps/raft` @ `56e32004` (unchanged).
Conventions: the bug-fix arc charter's (`docs/2026-08-19_bugfix-arc-charter.md`)
— guardrails first, predicted flips stated pre-run, same-commit re-pins.

---

## Item 1 — H-9, the inittask double-escape (BUG-064)

**Root cause, re-derived** (matches the W3 diagnosis, sharpened):
`buildInitGraph` (`tools/nativefrontend/load.go`) closes over the program's
imports with a worklist that mixed two NAMESPACES. Source units push their
imports as import PATHS; the closure loop pushes each table entry's `deps` —
which are linker symbol PREFIXES, gc's own R_INITORDER edges read from the
compiled archives, already percent-escaped — onto the same list, and applies
`pathToPrefix` to every popped item. `pathToPrefix` escapes `%` (objabi's
does; it must, or escaping wouldn't round-trip), so the stdlib's one escaped
prefix `crypto/internal/entropy/v1%2e0%2e0` became
`crypto/internal/entropy/v1%252e0%252e0` and `stdInitLookup` missed a row the
table has (line 64, unescaped path in column 4). The refusal message printed
the SINGLE-escaped name because it formats the popped item, not the lookup key
— which is why the message looked self-contradictory ("not in the table"
naming exactly a table row).

**Blast radius, measured from the table** (closure over `inittask-std.tsv`
dep columns): 39 non-internal std packages' init closures reach the escaped
prefix — the whole crypto family (`crypto/rand`, `crypto/sha256`, ..., via
`crypto/internal/fips140/drbg`), `net/http` and friends, `expvar`,
`go/importer`. Any MULTI-package program importing any of them refused.
Single-package programs are immune (`specInitOrder` returns early below two
source units — the init graph is never built), which is why the pre-W4 corpus
never saw it.

**Guardrails (landed first, red witnessed pre-fix):**

| case | shape | pre-fix | post-fix (predicted) |
|---|---|---|---|
| `multipkg/inittask-escape` | 2-pkg, blank `crypto/rand` (raft's route) | whole-export refusal (`frontend-export`) — witnessed 2026-08-20 against the unfixed frontend, exact message above | PASS |
| `multipkg/inittask-escape-closure` | 2-pkg, blank `crypto/sha256` — the escaped prefix arrives deps-of-deps, never named by the source program | same refusal — witnessed | PASS |
| `multipkg/inittask-escape-single` | 1-pkg, blank `crypto/rand` — the immunity control | EXPORTS clean — witnessed | PASS (must not move) |

**The fix:** the worklist carries PREFIXES only (`workItem{prefix, display}`):
source imports convert via `pathToPrefix` exactly once, on push; table deps go
on verbatim (`display` = the prefix — the unescaped path of a dep is not
recorded, and it is only a refusal-message string). Graph CONTENT is unchanged
(the `deps` arrays were always prefixes); only the closure's lookups change.
No wire, decoder, or table change. Frontend unit tests pass.

**Predicted flips for the full differential (stated before the run):** exactly
2 red→green (`multipkg/inittask-escape`, `multipkg/inittask-escape-closure` —
NEW ids recorded directly as PASS since guardrails and fix land in one
commit-group), 1 NEW green control (`inittask-escape-single`), zero movement
on all pre-existing ids. Baseline re-pinned same-commit with this reason.

## Item 2 — errors.New as a stdlib shim (G-2/H-10) — pending

## Item 3 — H-11, package-level var quarantine — pending
