# Pre-merge adversarial review — `land/i1-declarations` @ 8b4a1aec

Reviewer: the [AGENT] coordinator's Opus auditor, 2026-09-08, at the [USER]'s request
(«act as a reviewer for the worktree land/i1-declarations. After you review the agent
will fix and then land it»). The lane's agent fixes; the [USER] signs the merge.
Everything below was reproduced independently in this worktree's `.tmp/audit/`; nothing
tracked was modified.

## VERDICT: FIX-FIRST

(i) No wire byte changed for any corpus program — PROVEN: main's frontend vs the tip's
over 1,816 Corpus dirs + 7 raft dirs: `wire_diffs=0`. `wire.go`, `emit.go`, `identity.go`,
`NativeToIR.lean` untouched; no non-test caller of `emitDeclarationType`. Twin pin ok.
Merge-protocol 5a NOT owed.
(ii) The strict JSON boundary has NO silent value-normalization path (32 adversarial inputs
vs `Lean.Json.parse`; duplicate keys, lone surrogates, control chars, BOM, NaN, `+1`,
comments, trailing commas/garbage, non-RFC whitespace, `01`/`1.`/`.1`/`1e`, `1.0` for a
Nat — all REFUSE by name). Two resource-exhaustion ABORTS remain (R5, R6).

## Findings (fix R1–R3 before landing; R4 in the same pass; R5–R11 may be rowed)

R1 — HIGH — Declaration ids bypass `checkKeyPathGrammar`; the alarm is discarded with the
isolation clone. `tools/nativefrontend/declaration.go:140-143` mints the id via
`qualifiedTypeName` and checks only `e.substErr`; `pkgQualifier` (identity.go:95-104)
records a `keyPathHazard` into `badKeyPaths` (and `displayConflicts` into its list) on the
throwaway `declarationEmitter`, which is never consulted. Repro: path `example.org/foreign`
→ id `example.org/foreign.Named`, err=nil, while the same emitter's
`checkKeyPathGrammar()` = "import path(s) unusable as wire identity qualifiers"; likewise
`a·b`, `pkgs/naïve`. Every real module path has a dot, so the two identity channels
disagree on the whole non-main universe, unrecorded (F7 two-sources-of-truth).
`declaration_isolation_test.go:49-54` pins the acceptance. FIX: after `qualifiedTypeName`,
check `e.checkKeyPathGrammar()` and `e.displayConflictRefusal()` on the clone and return
them; OR record (tagged [USER]/[AGENT]) why the declaration key grammar admits what the
wire grammar refuses, with a control pinning that decision.

R2 — HIGH — The Lean decoder admits a package-less UNEXPORTED member id that the Go
producer refuses by name. `GoLean/NativeDeclaration.lean:46-51` (`memberId`) checks only
non-empty name + exact keys; producer refuses at `declaration.go:36-45`. Two packages'
unexported members both spelled `package:""` compare EQUAL. Repro:
`decodeBytes [] "{\"kind\":\"struct\",\"fields\":[{\"id\":{\"name\":\"x\",\"package\":\"\"},\"type\":{\"kind\":\"basic\",\"basic\":\"bool\"},\"embedded\":false,\"tagBytes\":[]}]}".toUTF8`
→ ACCEPTED. FIX: refuse a non-upper-case first rune with empty `package` (and an exported
name carrying a package); add both to `Tests/DeclarationWire.lean`'s reject list.

R3 — MED — Duplicate interface methods refuse (`canonicalMethods`, :71-81) but duplicate
struct FIELD names are accepted (:149-160). FIX: mirror the duplicate check for field ids
(order significant — refuse, do not reorder).

R4 — MED — `tools/declaration-audit.py:35` copies `.lake/build/lib/lean/{GoLean,Tests}`
six times into a `mktemp -d` under `${TMPDIR:-$ROOT/.tmp}` and never deletes it (:25):
~797 MB per `scripts/ci` run, and `TMPDIR` here is the PRIMARY checkout's `.tmp` (R11).
FIX: copy only what the poisoned module needs (or layer `LEAN_PATH`), delete on success,
retain only on failure.

R5 — MED/LOW — `GoLean/StrictJsonParse.lean:56-126`: unbounded `partial` mutual recursion;
depth 10,000 → "deep recursion was detected" abort (non-zero, but not a named refusal;
compiled = stack overflow). FIX: depth counter + `fail s!"{path}: JSON nesting deeper than
N"`; positive control at the limit, negative above.

R6 — LOW — Inherited from `Lean.Json.Parser.num`: `1e100000000` materializes a 10^8-digit
Nat; `1e10000000000` → `INTERNAL PANIC: Nat.pow exponent is too big`. Bound the exponent or
reject oversized/non-integral numbers before materializing.

R7 — LOW — `[01]`, `[.1]`, `[+1]`, `[NaN]` refuse with the container-grammar message, not
"leading zero"/"not a JSON number". Name the cause.

R8 — LOW (scoping) — There is no declaration SET, closure, or producer for the
`Nominals` inventory the decoder requires (only `declaration_fixture_test.go:65-70`'s
ad-hoc 3-entry list). The landing note discloses this; the chunk name invites the opposite
reading. Positive cross-checks passed: Alias/Unalias, constraints refused by name, generic
instantiation args ordered/distinct, `·N` ordinals per function, unexported names
package-qualified, raw tag bytes preserved, universe `error` vs fabricated `error`, 576/576
`types.Identical` pairs agree with JSON-byte equality.

R9 — INFO — Eleven new `unsup` formats, ten listed in
`tools/lowerdiag/unclassified-formats.txt`; `declaration method %s has no signature`
(declaration.go:237) is absorbed by the `frontend-invariant` row (causes.tsv:86).

R10 — INFO — `Tests/declaration-fixture/SHA256SUMS` has no re-pin guard (only README prose).

R11 — INFO — `scripts/check-declarations` scratch goes to `$TMPDIR` = the primary
checkout's `.tmp` (cross-worktree disk sink with R4).

## Closures verified

A-R11 CLOSED: `scripts/check-declarations:22-38` regenerates and `sha256sum --strict -c`
under `set -euo pipefail`, hard `bad` in `scripts/ci:481-487`; pristine emit = pin
`26748fff…3f3c` = the 2026-09-06 fresh fixture; an injected serializer drift moved the hash
and went red; negative control present.
A-R12 REPAIRED for the executable path (private `declarationEmitter`; outer registries
byte-identical before/after; whole-program re-emit identical) — at the cost of R1.
Auditor B's `declarationEntryKey`/`sealDeclarations` hazard does NOT apply: no `emit.go`
delta, no occurrence in the tree.
Reviewed-vs-integrated: `StrictJsonParse.lean`/`NativeDeclaration.lean` byte-identical to
the reviewed blobs at 7ac3eb46; `declaration.go` +51/−8, `scripts/check-declarations`
+24/−4, tests changed, `declaration_isolation_test.go` new — those repairs were reviewed by
no one but the author until this review (the note says so honestly). R1–R3 sit in exactly
that changed surface.

## Gate (my run, clean tree, 8b4a1aec, jobs 12)

ok evidence-on-main size gate · ok AGENTS.md alias · ok declaration boundary · ok frontend
pins · ok bug-index · ok eval tests (207) · ok negative baseline diff · ok baseline diff
FULL (3654/3654, no regression) · reconciler 2/0 HIGH · RESULT: PASS · git_dirty false ·
no baseline row moved · `--slow` certification at 3e393be5 verified (tree c55319ea…;
tip differs by six docs/evidence files only). Plan L1b path accounting reconciles: 16 + 15
extras = 31. New modules outside the default `golean` build; `DeclarationTests` built by a
real ci step (v2 §3.1 T8 does not recur). No sorry/admit/native_decide/axiom.

## Recommended disposition

Land after R1, R2, R3 are fixed (or explicitly ruled and recorded) and R4 in the same
pass; row R5–R11. Re-run `scripts/capped scripts/ci --diff` on the clean fixed tip
(GOLEAN_COVERAGE_JOBS ≤ 12, TMPDIR inside the worktree) and add the R1/R2/R3 negative
controls to the tests. The chunk's own landing condition is met and verified.
