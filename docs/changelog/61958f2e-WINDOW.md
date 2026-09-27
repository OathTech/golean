# Changelog `61958f2e` → the window's offer commit (LIVE draft)

[AGENT packet A worker] 2026-09-27 — window charter row 0 (`docs/2026-09-23_batched-window-charter.md` §1),
packet A brief `docs/codex-briefs/2026-09-24_packet-A-contract.md` §6, run as an Opus 5.5 subagent under the
execution-model ruling of 2026-09-27 (`docs/2026-08-31_qrow-rulings.md`, «E6's shape, train r49 and the execution
model — RULED (2026-09-27)»). `61958f2e` is the customer's pin (train r39 close, 2026-09-17). «Now» is `main` @
`5946adfa` (train r49 close; the packet's input commit — the brief's `3fb4a0d1` superseded by the coordinator:
`git diff --stat 3fb4a0d1 5946adfa -- GoLean/GoCore` is empty; r49 moved only the decoder and the frontend). The
packet branch was rebased onto `main` @ `7d2a62e5` (r49 5a records + r50 docs: no `GoLean/` change), so every cell
holds there too. It now sits on `core/stray-panic-refusal-0927` @ `05d0dbd4` (under audit), whose changes are the
window line below, not the table (its `GoLean/GoCore` edits are line-for-line, so every line number holds).

Every cell is RESOLVED from `git diff 61958f2e 5946adfa -- GoLean/` and `git show 61958f2e:<path>`; `file:line` is
at the commit named in its column (paths under `GoLean/GoCore/` unless given). `Tests/` is out of scope. Every
«what to touch» cell is an inference **[inf]**.

## Shapes changed since the pin

| Arm / shape | Before (61958f2e) | After (main @ 5946adfa) | What a re-pin must touch [inf] |
|---|---|---|---|
| `Step` arity | `inductive Step : Config → Store → Config → Store → Prop` (`Machine.lean:4390`) | `… → Store → AccessTrace → Prop` (`Machine.lean:5315`); `AccessTrace := List MemEvent` (`Ops.lean:1841`; `MemEvent = access \| hb \| attributed`, `:1821`) | [inf] every `Step` mention gains the label argument; `Prim`-style wrappers quantify or fix it |
| `stepFn`'s result | `Except Stop (Config × Store × Choices)` (`StepFn.lean:255`) | `Except Stop (Config × Store × Choices × AccessTrace)` (`StepFn.lean:326`) | [inf] every `stepFn … = .ok (c', s', ch')` premise gains a fourth component (`[]` on a pure step); destructuring lemmas bind one more |
| `stepFn_sound` / `step_complete` | `stepFn … = .ok (c', s', ch') → Step ctx c s c' s'` / converse `∃ ch ch'` (`MachineSound.lean:473`, `:819`) | `… = .ok (c', s', ch', tr) → Step ctx c s c' s' tr` / `Step ctx c s c' s' tr → ∃ ch ch', stepFn … = .ok (c', s', ch', tr)` (`MachineSound.lean:1681`, `:2079`) | [inf] every use: one more tuple component and one more `Step` argument, the same `tr` on both sides |
| read / write labels | no label (no `AccessTrace` type at the pin) | the emitting accessors: `Mem.load` → `[.access .read (.data l.canon)]`, `Mem.store` → `[.access .write …]`, map payload `Mem.mapRead` / `Mem.mapWrite` (`Ops.lean:1939`–`1968`) | [inf] read/write step equations name the singleton label |
| alloc label + `Store.alloc` | `Store.alloc : Store → GoValue → Ty → Loc × Store`, total, NO normalization (`Store.lean:41`) | NO alloc event (`AccessKind = read \| write \| atomicRead \| atomicWrite`, `Ops.lean:1745`); `Store.alloc : … → Except Stop (Loc × Store)` NORMALIZES the value at its type and refuses what the normalizer refuses (`Ops.lean:1251`); `HeapNormal ctx σ` is a `StateWf` conjunct (`StateWf.lean:708`) | [inf] allocation equations see a normalized cell and an `Except` result; `StateWf` users carry `HeapNormal` |
| `Trace.step` | `stepFn ctx s c ch = .ok (c₁, s₁, ch₁) → …` (`Trace.lean:18`) | `… = .ok (c₁, s₁, ch₁, tr) → …` (`Trace.lean:18`); `run_ok_iff` / `Trace.erase` statements textually unchanged (`Trace.lean:60`, `:42`) | [inf] none for users of `run_ok_iff` + `Trace.erase` only |
| `Step` rule count | 122 | 128 — added `unseqRunRecv`, `unseqRunAlloc`, `unseqRunWide` (`Machine.lean:6081`, `:6090`, `:6099`), `unseqRecvDone`, `unseqAllocDone`, `unseqWideDone` (`:6139`, `:6145`, `:6151`); none removed. Counting command, run at both commits: `git show <rev>:GoLean/GoCore/Machine.lean \| awk '/^inductive Step :/{f=1;next} f&&/^[^ -]/{exit} f&&/^  \| /{n++} END{print n}'` → 122 / 128 | [inf] an exhaustive `cases` on `Step` gains six arms |
| `Stmt` / `Cont` / `ChoiceSite` / `Config` constructors | 44 / 33 / 10 / 10 | IDENTICAL lists at both commits (verified by extracting each `inductive`'s `  \| ` constructor names from `Syntax.lean` / `Machine.lean` / `State.lean` at both revs and diffing: equal, in order) | [inf] none |
| the legacy `unseq-probe` triple | present | PRESENT and SURVIVES into the re-pin ([USER] 2026-09-27, rulings ledger above): `Stmt.unseqProbe` (`Syntax.lean:774`), `Cont.probeK` (`Machine.lean:3512`), `Step.unseqProbe` (`Machine.lean:6009`), `ChoiceSite.unseqPanic` (`State.lean:329`) | [inf] one extra `Cont` constructor and one `Step` rule to port; their retirement is a LATER removal-only change |
| the wire | no `"unseq"` statement key-schema in the decoder (`GoLean/NativeToIR.lean` @ pin: 0 matches) | `{"stmt":"unseq","cells","occs","stores","then"}` and eight occurrence kinds `eval`/`invoke`/`target`/`load`/`guard`/`recv`/`allocate`/`wide` (key schemas `GoLean/NativeToIR.lean:212` and `:898`–`905`); the map arms inside a graph carry `keyType`/`valueType` CHECKED against the base's declared type (`GoLean/NativeToIR.lean:1004`, `:1007`); no other key schema changed (diff of the decoder's `some [...]` key tables: additions only) | [inf] re-emit fixtures; a fixture whose statement fires the observability trigger now sees `Stmt.unseq` |
| the decoder's named refusals | 62 `fail` sites, 0 `unseq:` | 142 `fail` sites (`git show <rev>:GoLean/NativeToIR.lean \| grep -cE '(^\|[^A-Za-z])fail +(s!)?"'` → 62 / 142; audit F6), 80 `unseq:`-prefixed named refusals (`grep -c 'fail s!"unseq'`), all in the `unseq` grammar (`decodeUnseq`, `GoLean/NativeToIR.lean:2278`); incl. E6a's `after` edge on a literal `allocate` (`:2545`) and the scope-exact source-local checks (`:1189`, `:1195`, `:1201`); no non-`unseq` `fail` line added or removed | [inf] none for wires the frontend emits; a hand-built wire meets the refusals by name |
| the window's contract modules (packet A) | — | NEW, in the default build via `GoLean.lean`: `GoLean/GoCore/BridgeSet.lean` (24 pinned statements — a drift fails the build) and `GoLean/GoCore/ExecutionStatement.lean` (`Prefix`, `Finish` with FIVE constructors incl. `fatal` — [AGENT] coordinator disposition 2026-09-27 — `LRun`, `replays`, `NoRefusal`, the owed `_stmt` Props; statements only, packet B proves; audit F1 resolved by `core/stray-panic-refusal-0927`, disposition (b), [AGENT] coordinator, disclosed at the merge ask); one `scripts/mem-callsites.tsv` row («NO EXECUTION», `program_bridge_stmt`) | [inf] import the two modules; `BridgeSet.lean`'s diff between pins IS the interface diff |

## Window lines (landed since the pin, per lane)

- **E6a (2026-09-24) — the `unseq` grammar.** The observability trigger admits a FAILING occurrence unordered
  against an E1 participant's window that holds another failing occurrence or may itself fail (panic identity —
  the EVENT-MEDIATED form, a faithful subset of the ruled wording; the general form posed); `len`/`cap` over map /
  channel operands; callees and methods of EVERY source unit (bare, `pkg.F`-qualified, receiver-qualified) — sweeps
  in imported and stdlib source-through units lower as `unseq` graphs. A consumer of a GoCore program sees
  `Stmt.unseq` where the legacy `unseq-probe` / ANF hoist stood in those sweeps (14 corpus rows; the raft twin's
  `raft.isHardStateEqual`, `raft.MustSync`, `raftpb.(*Snapshot).SizeMessage` — admitted through the unit boundary
  by Stage E's E3 rule, not by the refinement; all-forced singletons). No core constructor, `Step` rule or choice
  site changed; the legacy triple stays (see below: it SURVIVES into the re-pin).
- **E6a — the wire decoder** (`GoLean/NativeToIR.lean`): two named refusals — an `after` edge on a literal
  `allocate` (`slice-lit`, `map-lit`, `new` over a `struct-lit`); a source-local atom whose `type` annotation
  disagrees with the declaration IN SCOPE at its statement, or which names no local in scope (`LowerCtx.locals` —
  scope-exact since the audit fix round: block / clause scope, the innermost declaration wins). Emitted wires are
  unaffected.
- **E6a — the raft twin pin** e1a87725… → 1c4e7038… (three graphs born by the unit boundary under E3's rule;
  `scripts/check-frontend-pins`).
- **E6a — the corpus**: `evalorder/unseq-strings/str-index-status-diverse` born (the first status-diverse `unseq`
  row); `builtins/e13-sibling-panic-order/assert-left-min-inline`, `channels/recv-order/dead-recv-len-operand`
  strict → membership.
- **E6a audit fix round (2026-09-24) — the corpus and BUGS.md**: BUG-116 filed (fixed) — a late-realized failing
  NON-CALL operand left of an inline `len` / `cap` / `min` / `max` whose operand panics, call-free, answered the
  LEFT panic on main where gc realizes the built-in's operand's; seven membership rows born in
  `builtins/e13-sibling-panic-order` (`idx-left-vs-min-operand`, `idx-left-vs-len-slice-expr`,
  `deref-left-vs-len-operand`, `ptr-field-left-vs-len-operand`, `div-left-vs-len-operand`,
  `shift-left-vs-len-operand`, `compound-load-vs-len-operand`); BUG-032's A6 sentence corrected. Baseline 3761 →
  3768 = 3532 / 236.
- **E6a audit fix round 2 (2026-09-24) — the wire decoder** (`GoLean/NativeToIR.lean`): the audit
  re-verification's R1, a FAIL-CLOSED WRONG REFUSAL introduced by fix round 1 — a `range` statement's key / value
  variables leaked into the ENCLOSING block, so a legal program that shadows an outer variable of another type
  with a range variable and graphs the OUTER one after the loop was refused whole (gc and main answer 23; the
  key-variable spelling 9). A `range` node now contributes NOTHING to the enclosing scope (`rangeBinderLocals`,
  opened by `decodeRange` for the body alone); the scope rule is stated once, with the construct table, as the
  docstring on `nestedStmtKeys`. NATIVE witness `e6arange` (the auditor's two positive controls verbatim + the h12
  base), mutant `mut-local-range-var-after-loop` (55 → 56). No corpus row, no baseline change, the choice trace
  byte-identical.
- **2026-09-27 core/stray-panic-refusal-0927** (packet A audit F1; disposition (b), [AGENT] coordinator, disclosed at
  the merge ask): root-only reader `loadRoot` (+ `Mem.loadBinding`/`loadBindingFor`) at the six binding-cell reads; a
  non-root location refuses as `.internal «binding cell is not a root location»` instead of escaping `stepFn` as an
  unwound Go panic (audit F1); `Step.evalVar`'s premise follows; no row moved. (The lane note's «changelog line»,
  `docs/2026-09-27_stray-panic-refusal.md`, verbatim.)
- **E6 re-scoped ([USER] Mike 2026-09-27, verbatim, relayed — rulings ledger «E6's shape, train r49 and the
  execution model — RULED (2026-09-27)»):** E6a lands; E6b–E6d and the retirement E6e LEAVE the window's critical
  path. The legacy triple `Stmt.unseqProbe` / `Cont.probeK` / `Step.unseqProbe` / `ChoiceSite.unseqPanic`
  SURVIVES into the re-pin offer — one extra `Cont` constructor and one `Step` rule to port; retirement becomes a
  later removal-only change.

(The E6a lines above are the E6a lane's «changelog lines», `docs/2026-09-24_unseq-stage-e6a-handoff.md` §«Changelog
lines for the window», folded here verbatim except the closing clause of the first line, which pointed at E6e.)

## Window rows (PENDING)

| Row | Line |
|---|---|
| E6e | OFF the critical path ([USER] 2026-09-27): no retirement in this window; the legacy triple SURVIVES (above). PENDING — filled by the landing lane, if any |
| label | PENDING — filled by the landing lane |
| P | PENDING — filled by the landing lane |
| C3 | PENDING — filled by the landing lane |
| B6 | PENDING — filled by the landing lane |
| C4 | PENDING — filled by the landing lane |

LIVE through the window; FROZEN at the offer commit (charter row 7).
