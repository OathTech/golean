# Review update (delta) — `land/i1-declarations` @ 4eb2ab1c

Reviewer: the [AGENT] coordinator's Opus auditor, 2026-09-08, second pass over the two fix
commits (061904f0 code, 4eb2ab1c records) landed after the first review at 8b4a1aec
(`2026-09-08_coordinator-review.md`). Everything reproduced in this worktree's
`.tmp/review2/`; nothing tracked modified. The [USER] signs the merge.

## VERDICT: MERGE-CLEAN

R1–R7 and R11 are CLOSED by independent reproduction; R8 and R10 remain disclosed
limitations (R10 wants a queue slot — N5 below). No new HIGH or MED finding. The chunk's
landing condition still holds: no wire byte changed for any corpus program.

## Closure table

| # | Sev | Status | What was re-run |
|---|---|---|---|
| R1 | HIGH | CLOSED | `declaration.go:30-41` consults the clone's `checkKeyPathGrammar()` + `displayConflictRefusal()` and returns them. Probes `example.org/foreign`, `a·b`, `pkgs/naïve`, `gopkg.in/yaml.v3` → REFUSE with the WIRE channel's text (one grammar; F7 drift closed); `foreign/path` still accepted; nested hazard `map[[3]*p.Named]chan p.Named` refuses. Isolation survives: outer emitter `%#v` identical before/after, whole-program re-emit byte-identical after a refusal. `declaration_isolation_test.go:54` now pins the refusal (+3 path rows, +1 display-conflict row); 8/8 subtests pass. |
| R2 | HIGH | CLOSED | `NativeDeclaration.lean:48-57`: unexported+empty package → `unexported member has no package identity`; exported+package → `exported member carries a package identity`; both arms for interface methods too; rejects in `Tests/DeclarationWire.lean:39-49`. EXPORTEDNESS PREDICATE: no producer/decoder split — `tools/declaration-unicode/main.go` generates `GoLean/DeclarationUnicode.lean` from Go's `unicode.Upper` tables and an oracle bitmap of `unicode.IsUpper` over all 1,114,112 code points; `scripts/check-declarations` regenerates + `cmp`s + runs the exhaustive test (gate line: `all 1114112 code points match Go unicode.IsUpper`). Spot-checked vs `go/token.IsExported`: `ǅ`/`ǅx` (U+01C5, Lt) not exported both sides; `Ǆ` (Lu), `Ωx`, `ẞx`, `𐐀x` exported both; `Ⅷx` (Nl) not exported both. First code point taken as Go's `utf8.DecodeRuneInString`; invalid UTF-8/lone surrogates already refused by the parser. |
| R3 | MED | CLOSED | `uniqueFields` (:75-82) refuses duplicate non-blank `MemberId`s, order preserved: `X,X`; embedded-vs-declared same id; `struct{p.T; q.T}` (both exported → ⟨T,""⟩) — matches Go (`types.NewStruct` panics on that shape); same-package `t,t`; repeated `_` accepted; `AB ≠ BA`. Rule = `go/types` `objset.insert` + `Id(pkg,name)` (cited, checked at deps/go). |
| R4 | MED | CLOSED, measured | `declaration-audit.py` symlink-overlays the first package component only, excludes the poisoned module + sidecars, deletes on success, retains + `failure.txt` on failure. After ONE gate run the scratch dir is gone (`scratch removed (6947764 owned bytes; dependencies symlinked)`); only two deliberate 16 K failure controls remain. Pre-fix leftovers still on disk in the primary checkout: 14 dirs, 1.3 GB, dated 2026-09-06 (cleanup is the [USER]'s call). `lakefile.toml` 2-line diff = `Tests.DeclarationUnicode` added to the `DeclarationTests` globs (built by a real ci step). |
| R5 | MED/LOW | CLOSED | Depth 64, named: `JSON nesting deeper than 64`; `decode (Json)` has its own 64 budget (`declaration nesting deeper than 64`); at-limit / above / 10,000 controls in `Tests/StrictJsonParse.lean`. |
| R6 | LOW | CLOSED | `1e100000000` → `JSON number exponent exceeds 1024 in magnitude` BEFORE materializing; the pre-fix parser recompiled from 8b4a1aec still `INTERNAL PANIC`s on it — panic → named refusal. |
| R7 | LOW | CLOSED | `[01]` → `leading zero in JSON number`; `[1.]` → `fraction needs a digit`; `[1e]` → `exponent needs decimal digits`; `[.1]`/`[+1]`/`[NaN]` → `invalid JSON number: expected integer digit`. |
| R8 | LOW | ROWED/disclosed, unchanged | No declaration set/closure/producer for `Nominals` (still the 24-type fixture's 3-entry list); master-plan-v2 R7 = PARTIAL / L1b OWED. |
| R9 | INFO | CLOSED mechanically | Ten formats in `unclassified-formats.txt` (dated [AGENT] note); the eleventh rides `frontend-invariant` (causes.tsv:86); `lowerdiag_test.go:719-731` hard-fails on drift (= ci step `lowering-diagnostic tables`, green). R1's refusal reuses the already-classified `frontend-apparatus` text. |
| R10 | INFO | OPEN, disclosed, NOT rowed | `SHA256SUMS` has only `sha256sum --strict -c`; no authorization guard analogous to the baseline re-pin guard. See N5. |
| R11 | INFO | CLOSED | `check-declarations:6-10` exports `TMPDIR="$ROOT/.tmp"`; Python hardcodes `ROOT/.tmp`. Verified: foreign `TMPDIR` ignored; zero new `declaration-audit-*` dirs in the primary checkout after my gate. (Overrides a caller's TMPDIR rather than defaulting — deliberate, commented.) |

Fixture pin did NOT move (diff empty; still `26748fff…3f3c`; re-derived from a fresh emit in
the gate: `declarations.json: OK` + negative control rejects changed bytes). Correct: R1 only
adds refusals; R2/R3 are decoder-side.

## No-regression evidence

- `git diff 8b4a1aec..4eb2ab1c -- tools/nativefrontend/{emit,wire,identity}.go GoLean/NativeToIR.lean` empty; no non-test caller of `emitDeclarationType`.
- Fresh corpus sweep main vs tip: `swept=1823 wire_diffs=0 refusals=452` (stdout + exit codes identical).
- `scripts/check-frontend-pins` ok (twin `758110a3f5a2…`).
- JSON parser differential, pre-fix (compiled from 8b4a1aec) vs post-fix, 53 inputs: LOOSENED = NONE; TIGHTENED = exactly the four declared budgets (`nested-65`, `nested-100`, `257-digits`, `1e1025`); all RFC-legal controls still accepted (`-0`, `2e1`, `1E+2`, `1e-2`, `0.5`, `[]`, `{}`, `""`, `\uXXXX` incl. a surrogate pair, `\/` + full escape set, 19-digit int, nested-64, 256-digit int). The declaration wire carries no exponents and only ≤19-digit lengths and tag bytes, so the budgets bite nothing real.
- Go tests: 9/9 `TestDeclaration*` pass. No `sorry`/`axiom`/`native_decide` in the new files; the four `partial`s are outside `GoLean/GoCore/`. New modules stay outside the default `golean` build. Evidence dir 36,469 B; the review copy byte-exact.

## New findings (none blocking)

- N1 — LOW — `NativeDeclaration.lean:75-82` ACCEPTS `struct{ p.t; q.t }` (two unexported same-name fields from different packages). Mirrors `go/types` `objset`/`Id` exactly (and `types.NewStruct` accepts it) — not an identity collapse — but unreachable from checked source (`Checker.structType` gives every field the declaring package), so the decoder's accept-set is strictly wider than the producer's image. Optional fix: require equal packages across a struct's non-blank unexported fields, or one sentence naming the residual. Resolve before a production consumer.
- N2 — INFO — `StrictJsonParse.lean:143` routes `+ . N I` into `boundedNumber`, so `[NULL]`/`[Infinity]` now say `invalid JSON number: expected integer digit` instead of `expected JSON value`. Named, fail-closed; message less apt.
- N3 — INFO (pre-existing on main) — `causes.tsv:85` classifies `import path(s) unusable as wire identity qualifiers` as `frontend-apparatus` ("a property of the tree"); a real module path is a property of the PROGRAM. R1 routes more traffic through it. For the coordinator, not this lane.
- N4 — INFO — `check-declarations:21` leaves one `declaration-fixture.XXXXXX` (248 K) per run; unbounded accumulation, small.
- N5 — LOW (process) — R10 is disclosed in `docs/2026-09-08_i1-review-response.md` but not rowed in master-plan-v2's owed tables. Per "every detected gap is rowed": add the row (or record a [USER] waiver) before merge. This is the only ask.

## Gate — clean tip 4eb2ab1c, jobs 12, TMPDIR in-worktree

ok evidence-on-main size gate · ok AGENTS.md alias · ok declaration boundary · ok frontend
pins · ok lowering-diagnostic tables · ok negative baseline diff · ok baseline diff FULL
(3654/3654, no regression) · reconciler 2/0 HIGH · RESULT: PASS · EXIT=0 · git_dirty false
(both metas name 4eb2ab1c). Lane's own gate: PASS at clean 061904f0; the tip differs by
docs/evidence only. 5a not owed.

## Disposition

MERGE-CLEAN. Ask the lane to row R10 (N5) — a one-line addition — then it is ready for the
[USER]'s merge sign-off. N1 may be fixed now or carried as a named residual.
