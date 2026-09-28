# Pre-merge audit — window packet B, the BRIDGES (2026-09-28)

[AGENT] auditor, under the [USER]'s every-merge-audited rule (relayed). Candidate `window/packet-b-bridges-0928` @
`ae37e5b8` = two commits (`f7b15450` proofs, `ae37e5b8` records) on `core/step-label-0928` @ `61bdc65d` (the label
reshape; its audit MERGE-CLEAN at `review/step-label-0928` @ `05435724`). Audit branch `review/packet-b-bridges-0928`.
No edit to the candidate or `main`; nothing merged or pushed. Evidence: `docs/evidence/2026-09-28_packet-b-audit/`.

## Verdict: MERGE-CLEAN

No blocking finding. Every packet-A statement is proved as stated; the proofs are sound (classical trio at most);
`stepFn_strict` is a whole-`stepFn` theorem. Two LOW records items and five follow-ups below, none of which changes a
statement, a proof or a runtime byte. The follow-ups in F5 and F6 should be settled BEFORE the re-pin offer to the
logic team, not before this landing.

## Attacks and results

1. **Statements unchanged.** `git diff 61bdc65d ae37e5b8 -- GoLean/GoCore/ExecutionStatement.lean` is comment-only:
   one header sentence plus twelve refreshed `file:line` references. No `*_stmt`, `Prefix`, `Finish`, `ZeroCost`,
   `NoRefusal`, `replays`, `LRun` or `Class*` body changed. The 23 `def <name>_stmt` and the 23
   `theorem <name> : <name>_stmt` in `Prefix.lean` match name for name (checked by `diff`). `Prefix.lean` defines
   no `_stmt` of its own and no shadowing def; since it shares the namespace, every theorem's type IS packet A's
   definition. `Machine.lean`'s diff is a comment (print arm); `MultiSound.lean`'s is the theorem-only F1
   strengthening of `stepThread_privateStep_label`: two extra conjuncts, proof extended, BridgeSet row 34 re-pinned.
2. **Soundness.** `#print axioms` over all 150 theorems in `Prefix`/`PrefixFacts`/`StepErrors` and the strengthened
   `stepThread_privateStep_label`: 50 use `[propext, Classical.choice, Quot.sound]`, 44 `[propext, Quot.sound]`,
   33 `[propext]`, and 23 use none (`axioms.txt`). No `sorry`/`admit`/`native_decide`/`decide`/`unsafe`/
   `implemented_by`/`opaque`/`axiom`/`partial`/`extern` in the three files. `import Lean` appears ONLY in
   `StepErrors.lean`. The brief and the handoff name PrefixFacts too, but PrefixFacts uses only `macro`s. The meta
   code is three tactic `elab`s (`errp_heq`, `errp_commit`, `errp_unfold`) plus macros. They build proof terms that
   the kernel checks. The only defs they touch are proof predicates (`ErrP`, `OkP`, `CommitOk`, `Stop.Strict/Tame`,
   `Config.blockedB`, `seqPicks`). No core module imports any of the three: they are reachable only through
   `GoLean.lean` → `Prefix` (and `BridgeSet`). `Main.lean` already imports `Lean.Elab.Term`. Gate: core totality
   audit, engine isolation and the escape-hatch preflight all ok. `check-core-audit` EXIT=0.
3. **`stepFn_strict` covers all of `stepFn`.** The hypotheses are `c.abort? = none` and `c.blockedB = false`, and the
   proof runs `fun_cases stepFn` over every arm. The two excluded classes are exactly where `stepFn` must raise
   something outside `Strict`: the deadlock at the four blocked forms, and the panic terminal or renderer refusal at
   an abort. `stepFn_error_cases` classifies both, so every error `stepFn` can raise is classified. Helpers are
   proved `Tame` under `toResult` (which turns a panic into `.ok (.panic _)`, `Value.lean:394`) and `Strict` when
   raw. Commit phases get `CommitOk`. This is a machine check that the stray-panic lane's six sites (`loadRoot` /
   `Mem.loadBinding(For)`, present at `Ops.lean:1390/2006/2012`) were the complete set. `#eval` witnesses
   (`witnesses-out.txt`):
   - integer divide by zero at a `strictK .div` apply → `.ok (.panicking …)` (unwinds);
   - the S6 witness → `.refusal (.internal "binding cell is not a root location…")`;
   - the abort configuration → the only panic terminal;
   - unlock of an unlocked mutex → `fatal`;
   - `.next .stop` → `.internal "step on terminal configuration"`.

   `stepFn_no_stray_panic rfl` closes the first witness's no-panic goal for every tape. A kernel-checked lemma
   cannot be broken by an `#eval`: the witnesses are sanity checks, not attacks.
4. **`stepFn_consumption_some'`** has a proof body byte-identical to `MachineSound.stepFn_consumption_some`
   (`MachineSound.lean:6219`). Its statement is identical minus the `(_hloc : c.appendTargetLocal)` binder, which
   the original never reads, so it is strictly STRONGER, not weaker. Follow-up F3.
5. **`classification_wf` / `noRefusal_step`.** Both are sound. The unused `StateWf` does NOT mean `NoRefusal` is
   too strong. It means the corollary is almost definitional: `classification_strong` puts case 4 at a
   `Prefix`-reachable non-zero-cost refusing `stepFn` call, and `NoRefusal`'s first clause forbids exactly that.
   All of the domain content sits in `NoRefusal`. It is not vacuous: packet A's positive control holds, and
   `noRefusal_step` proves one-step preservation with no `StateWf`, using `stepFn_any_residual`. For a real lowered
   program's initial configuration, `NoRefusal` quantifies over every tape and every reachable non-zero-cost
   configuration, on the SEQUENTIAL driver. It fails for any program that reaches a `go` statement
   (`StepFn.lean:807/814` refuses the spawn outside the pool). It also fails for any program that reaches an
   unsupported feature on some schedule. For a goroutine-free program inside the supported fragment, nothing in
   the definition makes it unsatisfiable: its reachable configurations are exactly those the differential corpus
   runs without refusal. I did NOT construct a proof of it for a lowered program (see "Not verified"). F4.
6. **Omissions (brief items 7b and 9).** The pool half is NOT owed inside this landing. Charter §2 says: «The pool
   half WAITS for: the labelled pool relation over `StepLabel` … (`program_run_iff`, `observation_iff`
   relabelled) … after the window». Packet A's `program_bridge_stmt` disclaims it («NOT counted as a bridge»), and
   the brief's own item 9 contradicts the charter. Nothing is stale: `ProgramRun`/`program_run_iff`/
   `observation_iff` go through `Pool.Run`, which folds `ev.out` = `ev.label.out` (`PoolTrace.lean:75`). They build,
   and they are core-audit-required. What IS missing against response §2/§3 is the single-goroutine OUTPUT
   agreement (the pool's `out` fold = the sequential labels' `out` fold; `execProgLoopOut_snd` relabelled) and the
   sequential-to-pool projections for terminal events (only `.privateStep` is projected). F5.
7. **Required list.** Unchanged at 55; `requiredModules` names none of `ExecutionStatement`/`Prefix`/`PrefixFacts`/
   `StepErrors`/`BridgeSet`. BridgeSet pins the theorems' types, but deleting a row together with its theorem would
   pass both guards. F6.
8. **Records.** BridgeSet: a verbatim scratch copy compiles (EXIT 0). Each of three mutations fails with a type
   mismatch (EXIT 1 each):
   - row 45 re-targeted to `run_deadlock_iff_stmt`;
   - row 58 without its `c.abort? = none →` premise;
   - row 62 with an extra conjunct.

   Row line numbers spot-checked (`:373`, `:398`, `:578`, `:70`–`:592`): correct. The changelog «bridges (2b)» row
   matches the diff: 23 statements, row 34 changed, rows 35–64 added, seven supporting facts. The handoff is
   honest: its §6 flags are real interpretations, disclosed; its gate claims reproduce (below). F1, F2.
9. **Gate at `ae37e5b8`** (under the lock): `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` → EXIT=1, 775 s.
   It is red on EXACTLY the 5a pair: `certificate provenance` (STALE: changed dependency `GoLean.lean`) and the one
   drift line `imported-goose/channel/google-search PASS→FAIL/membership`. There are 3768 cases (3531 / 237); no
   other row moved; the negative baseline (394) matched; eval tests are 295 ok; the core build is warning-free;
   every other step is ok. Separately, `scripts/capped lake build` EXIT=0 (106 jobs) and `check-core-audit` EXIT=0.

## Findings

- **F1 (LOW, records/interface).** BridgeSet rows 35–57 pin by NAME: `example : X_stmt := @X`. The header's
  convention is «binders written out», and the header claims «the file's diff between two pins IS the interface
  diff». Neither holds for these rows: an edit to a `_stmt` body in `ExecutionStatement.lean` changes no line of
  BridgeSet. This is exactly the device's disclosed limit («a changed definition with an unchanged type»), now
  applied to the central contract. It is not silent, because the edit shows in `ExecutionStatement.lean`'s own diff
  and usually breaks a proof. Remedy (follow-up): write the types out (`Witnesses.lean` shows the delta check
  works), or state in the header and the changelog that `ExecutionStatement.lean`'s diff is part of the interface
  diff.
- **F2 (LOW, records).** The BridgeSet header's RE-PIN 2 paragraph says «rows 35–63 ADDED — the 23 proved `_stmt`
  theorems and six supporting facts». The file, its section heading, the handoff and the changelog all have rows
  35–64 and SEVEN facts (`noRefusal_step` was added late). Fix the sentence at the landing's records commit.
- **F3 (follow-up).** Fold `stepFn_consumption_some'` back into `MachineSound`: drop `_hloc` from
  `stepFn_consumption_some`, update its caller `MultiStreams.lean:564` and the `Tests/UnseqSchedulerAudit.lean`
  reference, delete the copy (about 240 lines of re-elaborated case sweep), and re-target BridgeSet row 62. Doing
  it right after the landing is best, because the duplicate costs build time and invites the two to drift.
- **F4 (INFO, disclose at the offer).** `classification_wf`'s `StateWf` premise is decorative, and `NoRefusal` is
  the whole domain obligation. It is sequential-driver-scoped: it excludes every program that reaches `go`. The
  offer should say so plainly, because the statement's `StateWf` suggests heap well-formedness is doing work. It
  isn't: `step_preserves_wf` is never used.
- **F5 (follow-up, BEFORE the re-pin offer).** Either prove the single-goroutine output agreement
  (`execProgLoopOut` under `execProgLoop_single`'s premises folds the same `out` as the sequential labels) and the
  terminal-event projection, or list both explicitly among the offer's LIMITS next to «the pool half waits». The
  logic team asked for these in response §2 («output … in one composable account») and §3 («Prove the
  sequential-to-pool projections, including attribution and terminal events»). Not FIX-FIRST: the charter defers
  the pool half, and no packet-A statement claims it.
- **F6 (follow-up).** Add to `Tests/GoCoreAudit.lean`, at the landing or right after it:
  - `requiredModules`: `GoLean.GoCore.ExecutionStatement`, `…Prefix`, `…BridgeSet`;
  - `exports`: the 23 bridge theorems (at minimum `prefix_iter`, `run_ok_iff`, `run_panic_iff`,
    `run_deadlock_iff`, `run_fuelOut_iff`, `finish_abort_step`, `replay_coverage`, `classification`,
    `classification_wf`), plus `stepFn_strict`, `stepFn_no_stray_panic`, `stepFn_error_cases`, `execStmtLoop_error`,
    `noRefusal_step`, `stepFn_picks_none` and `stepFn_picks_some`.

  The edit is to `Tests/`, so it belongs to the coordinator or a follow-up lane.
- **F7 (INFO, cosmetic).**
  - `errp_unfold` keeps a debugging `logInfo m!"RECURSIVE {n}"`. It fires only on a branch that `first` backtracks,
    and the build is warning-free.
  - Proof-layer definitions sit in core namespaces: `GoLean.Stop.Strict`/`Tame`, `Machine.Config.blockedB`, and a
    public `controlBadEntry`.
  - BridgeSet row 59 pins `blockedB`, a proof-module Bool. A `¬ Blocked c` form would suit the logic team better.

## Not verified

- A proof that `NoRefusal` holds for a real lowered program's initial configuration. §5 gives only an argument,
  plus packet A's one-step control.
- `release-check` / `build-certified`: that is the train's 5a work.
- The raft twin and the whole-corpus choice trace: the reshape lane ran them, and this packet changes no runtime
  byte (the gate moved no row).
