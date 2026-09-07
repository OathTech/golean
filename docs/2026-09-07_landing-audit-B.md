> **Landing preface ([AGENT] landing chunk L6 `land/sprint-records`,
> 2026-09-07).** Landing review of branch `typed-consumer-sprint` @
> `7edc298f` by the independent auditor B (2026-09-07), landed VERBATIM from
> the sprint worktree's scratch (`.claude/worktrees/typed-consumer-sprint/.tmp/landing-review/auditor-B.md`),
> where it was untracked; it is the source of every `B-Rn` finding id in
> `docs/2026-09-07_typed-sprint-landing-plan.md` and the chunk notes.
> Nothing below is edited. It describes the branch and the sprint WORKTREE
> as they were BEFORE the landing (the dirty staged `uintptr` merge, the
> storage-maintenance overlay, the evidence payload); which findings each
> landed chunk closed, and which remain open, is recorded in the chunk notes
> (`docs/2026-09-07_land-{gate-tooling,typed-core-proofs,observer-terminal,panic-text-tape}.md`)
> and summarized in `docs/2026-09-05_master-plan.md` §7.8. Paths of the form
> `.tmp/landing-review/…` are the auditor's scratch; the evidence it cites
> under `docs/evidence/2026-09-06_*` is on the archive branch
> (`docs/evidence/2026-09-05_typed-consumer-sprint/MANIFEST.tsv`).

# Landing review — auditor B (contract claims, records/provenance, evidence payload, landability)

Branch `typed-consumer-sprint`, tip `7edc298f`, 96 commits ahead of `main` `47195683`.
Worktree `/home/dev/projects/golean/.claude/worktrees/typed-consumer-sprint`.
Auditor B scope: contract claims vs the 2026-09-05 gate audit's F2/F3/F5; records
and provenance; the evidence payload; the landability partition.
Auditor A owns semantics / trust surface / gate integrity concurrently.

## VERDICT: DO-NOT-LAND as one train step. SPLIT, and LAND-AFTER-FIXES.

The proof work is real, non-vacuous, kernel-checked on the allowed axioms, and
answers a substantial part of F5 and the legitimate variant of F3. It is worth
landing. **It cannot land as this branch**, for three independent reasons:

1. The branch tip is not the reviewed artifact. The worktree carries **272
   staged-but-uncommitted files (+74,829/−222)**, including the trusted surface
   (`GoLean/NativeToIR.lean`, `tools/nativefrontend/atomics.go`), plus 47
   unstaged files (+694/−533) and 15 untracked files. The sprint's own state
   record is **untracked** and says the sprint is **PAUSED BY USER** with all of
   O1–O5 still mandatory (R1 below).
2. The evidence payload — **734,510 added lines across 2,159 files** under
   `docs/evidence/`, 24× the entire rest of the branch's additions — is not
   auditability, it is a duplicate of the repository (R7).
3. `CLAUDE.md` and `AGENTS.md` are amended on/над the branch in ways that widen
   agent authority beyond the quoted [USER] approval, including an uncommitted
   **standing approval to delete worktrees** (R5, R6).

Recommended shape: **four branches** (§6).

---

## 1. The F2 / F3 / F5 answer table

| Finding | What the branch actually proves | Domain / premises | Verdict |
|---|---|---|---|
| **F2** driver↔relation bridge | *Nothing new.* The stream-quantified bridge is **pre-existing on `main`**: `GoLean/GoCore/PoolTrace.lean:71 run_iff`, `GoLean/GoCore/ProgramTrace.lean:26 program_run_iff`, `:53 exists_program_run_iff`, `:75 observation_iff` (`∃ fuel ch` on **both** sides), with the two-outcome example at `Tests/InterfaceContract.lean:164–185` (`two_choice_pool_bridge`). The branch adds `Tests/InterfaceContract.lean` +1 line. | The branch's *typed* readouts (`BooleanPool.lean:161`, `RecoveryTerminal.lean:83`) are `∀ fuel, ∀ ch` but over profiles with **no choice sites**: `Control.no_spawn/no_select/no_seq_consumption`, `Inv.run_choices : chf = ch`, `Choices.consumeAtE … = (0, ch, [])`. | **Partially answered, but not by this branch, and not for the typed profile.** The `∀ ch` quantifier on the typed theorems is *vacuously uniform* — the profiles are deterministic. The reverse direction (relation → driver) for the true Prop-level relation is still absent: `Trace.erase` gives `Steps`, and `GoLean/Interface.lean` states "no converse to erasure is supplied". `ProgramRun`/`Pool.Run` are *mirrors of the driver*, not `Machine.Step`. See R2. |
| **F3** context laws / `EctxLanguage` | The branch does **not** attempt `step_fill`. It **sidesteps legitimately**: `spikes/gate-a1/GateA1/Language.lean:28` gives a plain `instance : Language Config ExecState Empty Unit` (PrimStep = `Step`), and the recover rule keeps the continuation explicit in **both** parameters and postcondition — `pure_recover (env) (k) : PurePrimStep (Config.evalE .recoverCall env k) (.retV (recoverResult k).1 (recoverResult k).2)` (`:53`), `wp_recover` (`:64`). Header, `:6`: "This has no `EctxLanguage` instance". This file is **also pre-existing on `main`**; the branch adds the customer proofs above it. | Sequential, `Unit` terminal, empty observations, uncaught panic is stuck. | **Answered, honestly, by the "basic `Language` without `EctxLanguage`" route the audit itself allowed.** It is **not** an `EctxLanguage` instance and does not claim to be. `spikes/iris-customer/README.md:85` repeats "There is no unconditional `EctxLanguage` or continuation-transport law." **Reviewer's counterexample reproduced UNCHANGED on the branch** (I re-ran `docs/evidence/2026-09-05_project-gate-audit/ContractProbes.lean` at the tip): `recoverResult bareFrame = nil`, `recoverResult panicFrame = interface (defined 1) (string "audit")`. It is neither excluded by admission nor side-conditioned — it is *made irrelevant* by parameterising every rule on `k`. That is the correct design, and the sprint says so. |
| **F5** typed admission / refusal freedom | **Real and substantial.** Two independently defined judgments with total checkers and soundness **and** completeness: `GoLean/GoCore/BooleanTyping.lean:336 TypedBooleanAdmission`, `:379 checkTypedBoolean`, `:392 checkTypedBoolean_iff`; `GoLean/GoCore/RecoveryAdmission.lean:83 RecoveryAdmission`, `:155 checkRecovery`, `:166 checkRecovery_iff`. All-successor preservation over the **Prop-level relation**: `BooleanPreservation.lean:150 Inv.step (hstep : Step c s c' t) : Inv … t c'` and `RecoveryInvariant.lean:43` (same shape); progress `BooleanSafety.lean:16 Inv.reachable_progress`, `RecoveryInvariant.lean:70` (normal terminal ∨ nonempty abort ∨ legal successor). Driver refusal-freedom, universally quantified over fuel and stream: `BooleanPool.lean:175 runProgramPool_no_refusal`, `RecoveryTerminal.lean:99/107`. | `TypedBooleanAdmission = BooleanAdmission ∧ ProgramTyped p`, checked over **every** function in the program (`ProgramTyped`, `:331`). Boolean profile grammar is `var/boolLit/not/and/or` + `seqn/block/initialization/assign(var)/ifThenElse/return` — **no calls, no loops**. Recovery profile adds direct/closure calls, defers, string panic, recover, finite call-graph certificate. | **Answered *within two deliberately tiny profiles*, and stated as such.** The reviewer's ill-typed cell is now excluded — I proved `¬ BooleanRuntime.BoolHeap illTyped` at the tip (`BooleanStore.lean:15` requires `.value .bool (.bool b)`). **But `StateWf` itself is unchanged**: `decide (StateWf illTyped)` still returns `true` at the tip. The exclusion is profile-local, not machine-wide, and F5's general `Accepted`/`WireWellFormed`/`ProgramWellTyped` programme is untouched. |

### Vacuity / non-emptiness — checked, not assumed

Verified at the branch tip by `scripts/capped lake build InterfaceTests
BooleanTypingTests BooleanRuntimeTests RecoveryTypingTests RecoveryControlTests
RecoveryTerminalTests` → **exit 0, 111 jobs**, and by elaborating my own probe
against the built environment:

- Axioms are clean — `checkTypedBoolean_iff` and `checkRecovery_iff` depend on
  `[propext, Quot.sound]`; `runProgramPool_typed`, `runProgramPool_no_refusal`
  (both profiles) and `observation_iff` on `[propext, Classical.choice,
  Quot.sound]`. No `sorry`, no `native_decide`, no new axiom.
- Admitted sets are inhabited by the *claimed native fixtures*, by kernel
  computation (`with_unfolding_all rfl`), not by assertion:
  `Tests/BooleanTypingFixture.lean:38–50` admits all four functions of
  `Tests/boolean-typing-fixture/main.go`; `Tests/RecoveryA2Artifact.lean:100–106`
  admits the complete A2 artifact at all three entries;
  `Tests/RecoveryTypingFixture.lean:391–412` admits the second fixture at
  `Shared/Outside/SharedFalse/SharedTrue/Reversed/DirectRecoveryControl`.
  `#eval checkTypedBoolean nativeFixture "Argument" #[.bool true]` → `Except.ok ()`.
- The A3a unbound counterexample is rejected with a *named cause*:
  `Tests/BooleanTyping.lean:22 old_unbound_rejected … = .error (.scopedBody ⟨"F"⟩)`,
  plus `unbound_write_rejected`, `use_before_declaration_rejected` — while
  `Tests/GoCoreAdmission.lean:102 unbound_accepted` is retained side by side, as
  the charter required.
- The second O2 fixture (`Tests/recovery-typing-fixture/main.go`) meets the
  charter §3.2 shape exactly: input-dependent result, ordinary helper call
  (`flip`), two deferred handlers sharing one captured result cell whose
  registration order changes the answer (`Shared` vs `Reversed`), the required
  negative control (`Outside` — recover outside an effective direct handler,
  admitted, returns nil), and a direct-vs-indirect discrimination control
  (`DirectRecoveryControl`). Five real differential rows in
  `Tests/recovery-typing-fixture/manifest.tsv`.
- Reuse is real, not a whitelist: `wp_call`, `wp_store_cell`, `wp_initialize`,
  `wp_frame_result` are each applied in **both** the A2 example
  (`spikes/iris-customer/GoLeanIris/Examples.lean`) and the shared fixture
  (`Shared.lean`, `SharedRecovery.lean`).

**Caveat on my own verification (do not over-credit it):** the build and probe
ran against the *working tree*, which is tip + the staged `uintptr` repair
(3 lines in `Machine.lean`, 4 in `Value.lean`, 2 in `Syntax.lean`, 3 in
`Platform.lean`), not against a clean checkout of `7edc298f`. No
`Boolean*`/`Recovery*` module is in the dirty set, so the contract results are
tip-accurate; the trusted-surface files are not.

---

## 2. The Iris customer facade

- **Iris is NOT a dependency of the default build.** Root `lakefile.toml` has no
  `[[require]]` at all; the branch's only change is ten new `lean_lib` test
  globs. Iris is required only in `spikes/gate-a1/lakefile.toml` and
  `spikes/iris-customer/lakefile.toml`, both pinned to
  `rev = e7a0a43814c4f1154ca0c8049883ca56c2288b86` — the same revision the gate
  audit's F3 cites. Charter/plan claim upheld.
- **Nothing in `GoLean/` or `Tests/` imports `spikes/`** (grep for `Iris`,
  `GateA1`, `GoLeanIris` over all `^import` lines in both trees: zero hits).
- **What it proves:** real Iris WP derivations, not computations —
  `spikes/iris-customer/GoLeanIris/SharedRecovery.lean:10 wp_shared_recover_handler`
  with heap points-to for the captured root and its pointee, discharged through
  `wp_call`/`wp_indirect_body`/`wp_frame_result`/`wp_store_cell`; whole-program
  results via `SharedDriver.lean:35 shared_program`, `:40 shared_program_result`,
  `shared_program_all_choices`.
- **The "no unfolding of internals" bar is NOT met, and the README says so**
  (`spikes/iris-customer/README.md:98`): "It still uses machine internals and
  unfolds operations". That is honest, but it means Gate C's exit criterion
  ("a consumer proof/example using the public interface without unfolding
  implementation internals") is **not** discharged. Do not let a landing note
  imply otherwise.

---

## 3. Findings

### R1 — BLOCKER — the tip is not the artifact; 74,829 uncommitted lines including the trusted surface

`git status --short` in the sprint worktree: **334 entries**.
`git diff --cached --stat HEAD` → **272 files, +74,829/−222** staged and *not
committed*, of which 248 are `docs/evidence/`. The non-evidence remainder is the
BUG-107 `uintptr` repair and it lands squarely on the trusted surface:

```
5  5  GoLean/NativeToIR.lean
2  2  tools/nativefrontend/atomics.go
4  0  GoLean/GoCore/Value.lean
3  3  GoLean/GoCore/Machine.lean
3  2  GoLean/GoCore/Platform.lean
2  2  GoLean/GoCore/Syntax.lean
26 0  baselines/native-full.tsv
3  8  tools/coverageharness/main.go
```

plus **47 unstaged files (+694/−533)** — `scripts/ci`, `scripts/diff-coverage`,
`scripts/check-interface.py`, every `tools/*-audit.py`, both `gate_checks.py`,
`AGENTS.md`, `docs/agent-sandbox.md` — and **15 untracked files** including
`scripts/go-cache`, `tools/storage*.py`, and five `docs/2026-09-06_*.md`.

Consequences:
- `GoLean/NativeToIR.lean` is touched ⇒ merge-protocol **5a** fires: `scripts/ci
  --slow` at the merged tip plus a refreshed certification record. The sprint
  itself records this as **owed** (`handoff:810` "measured combined baseline and
  slow gates owed"; `docs/2026-09-06_typed-sprint-pause-state.md:63` "The staged
  baseline is **PROVISIONAL** 3,643 = 3,399 PASS + 244 FAIL, an exact three-way
  union, **not a measured combined full run**").
- Charter §6 requires "Final evidence must cover the final source, not a
  neighboring tip." The late gate runs in this worktree ran against a tree that
  is *no commit at all*.
- A **second, unrelated workstream (storage-maintenance) has leaked uncommitted
  into the sprint worktree**, mutating `scripts/ci` and the whole audit tool
  set. This violates charter §5 ("Each writer owns a separate worktree … No
  agent writes into another agent's worktree") in effect if not in letter.

**Fix (blocking, before any landing conversation):** either complete or abandon
the staged `5f185fb3` merge as its own commit; move every storage-maintenance
edit out of this worktree; get to a clean tree at a named commit; re-run
`scripts/ci --diff` and `--slow` there; then re-open the landing review against
that commit. Snapshot `snapshots/typed-sprint-before-uintptr-20260906` exists
(`7edc298f`) — good practice, keep it.

### R2 — HIGH — F2 is not answered for the typed profile, and `∀ ch` reads stronger than it is

`GoLean/Interface.lean:66–70` says `runProgramPool_typed` gives readout "for
every supplied stream", and `:113` "for every fuel and supplied choice list".
True, but the Boolean and recovery profiles contain **no choice site**:
`BooleanPool.lean:16 Control.no_abort`, `:24 Control.no_select`,
`:18 Control.no_spawn`, `:181 Control.no_seq_consumption`, and the singleton
step consumes zero choices (`Choices.consumeAtE … = (0, ch, [])`,
`BooleanPool.lean:88`). A reader of the facade docstring can reasonably conclude
the typed contract has been exercised against nondeterminism. It has not. The
F2 two-outcome demonstration lives only in the *untyped* pre-existing bridge
(`Tests/InterfaceContract.lean:183`), and there is no result connecting it to
the typed profiles.

**Fix:** one sentence in `GoLean/Interface.lean` stating that both typed
profiles are choice-free, so the stream quantifier is uniform-by-vacuity and
carries no nondeterminism evidence; and record F2 as *still open for the typed
contract* in the master plan §7 table.

### R3 — HIGH — the R-1 ruling is stretched from "quotient the text" to "emit a rendering gc cannot emit", converting a fail-closed refusal into an answer

`GoLean/GoCore/Machine.lean` replaces `asciiString?` (fail-closed on any byte
≥ 0x80 **and** on an embedded newline — "a rejected payload aborting is a
visible unsupported, never a wrong message") with a **total** renderer:

```lean
def renderStringMember (s : GoString) : String :=
  match utf8String? s.bytes with
  | some text => if text.toUTF8.data == s.bytes then text else PanicText.escapeAllBytes s
  | none => PanicText.escapeAllBytes s
...
| .interface .string (.string s) => some (renderStringMember s)   -- was: asciiString? s.bytes
```

and the docstring asserts "R-1 authorizes a uniform ` [recovered]` suffix".

The citation is **not invented** — R-1 is a genuine [USER] ruling
(`docs/2026-08-20_w32-re-envelope-charter.md:26–58`, `:328–345`), it does name
`[recovered, repanicked]` as spec-silent latitude, and it does keep the forced
half (occurrence, payload KIND, control flow, exit) exact. `docs/2026-09-06_string-panic-member-assessment.md:8–17`
cites it by line and argues the extension explicitly. That is good practice and
I credit it.

Two things nonetheless remain unsettled and are **not** the sprint's to settle:
1. **Scope.** R-1's own text scopes itself to §S3(b) — "C3 (BUG-059
   panic-qualifier) and C4's remaining three (BUG-004 abort rendering)". The
   sprint extends the membership quotient to a **new family**, explicit string
   panic payloads, which previously matched gc exactly *or refused*.
2. **Envelope membership.** R-1 admits "the **conforming** renderings". A quoted
   `\xHH` escape of an invalid-UTF-8 payload is not a rendering any Go
   implementation produces; the pinned spec's `Handling_panics` requires "an
   error report including the panic argument's value". Calling it a member makes
   the row green against *our own pin*, not against Go. `baselines/native-full.tsv`
   is candid about this ("PASS/string-member means the reviewed R1 member, not
   exact gc text") — but candour in a baseline header is not a ruling.

Under charter K3 ("**Defer** new semantic-policy choices") and §7 ("choose among
unresolved interpretations of Go latitude" = critical issue → freeze, present at
closing), this is a closing-packet decision, not a landed fact.

**Fix:** carry the rendering change on its own branch; put "does R-1 extend to
explicit-string payloads, including a non-Go-producible escape member for
invalid UTF-8?" in the closing decision packet as an explicit [USER] question.
Do not land it inside a proof-modules train step. (Auditor A owns the semantic
merits; I own the claim that a ruling authorises it.)

### R4 — HIGH — `CLAUDE.md` retitles the merge protocol, silently narrowing gate-green and audit-ask to main merges only

`CLAUDE.md` (committed on the branch):

```diff
-## The merge protocol (exact, every time)
+## The merge protocol (to main, exact, every time)
+
+[USER] clarified 2026-09-05: merges **to main** always require user
+approval. Agents may merge into feature branches when the user has given
+standing approval for that work. …
```

The quoted K4 clarification is about **approval authority** only: "merges *to
main* are always user-approved. Feature branches can be merged to by agents,
when standign approval is given by the user"
(`docs/2026-09-05_typed-consumer-sprint-charter.md:3–7`, §2). Retitling the
whole numbered protocol "to main" scopes steps 2 ("gate green"), 3 ("the audit
ask — never skipped"), 5 (`--ff-only`) and 6 ("clean, green") off feature-branch
merges. K4 said nothing about gates or the audit ask. With 96 commits of
agent-to-agent feature merges, that is not a cosmetic edit.

Secondary: the paragraph is a **paraphrase**, not the verbatim [USER] text, and
is not marked "relayed by the [AGENT] coordinator — cite as relayed", which is
this repo's stated convention for every other [USER] quote in `CLAUDE.md`.

**Fix:** restore the heading to "The merge protocol (exact, every time)"; add
the K4 sentence as a note *inside* step 5 scoped to approval only; quote the
[USER] text verbatim and mark it relayed. The `AGENTS.md` committed addition
(a pointer to the sprint charter and handoff) is fine as-is.

### R5 — BLOCKER — an uncommitted `AGENTS.md` edit grants agents standing approval to delete worktrees

`git diff -- AGENTS.md` (unstaged, +34):

> `- [USER], 2026-09-06: the storage-maintenance charter authorizes the narrow
>   lifecycle in tools/audit_scratch.py …`
>
> `## Retired Worktrees`
> `[USER], follow-up to the 2026-09-06 storage maintenance: retired worktrees
>  (merged to main) are disposable. **Do not create or retain whole-worktree
>  archives.** … **This is standing approval for routine retirement of finished,
>  merged lanes.**`

This amends the operating charter's own rule three lines above it ("Do not run
`rm`, `rm -r`, or `rm -rf` without explicit approval") into a **standing
permission for a destructive operation**. Neither [USER] statement is quoted
verbatim, neither is marked relayed, and the charter it points to
(`docs/2026-09-06_storage-maintenance-charter.md`) is **untracked**. It is also
outside the sprint's approval list (K1–K5 say nothing about storage or worktree
lifecycle) and directly contrary to the user's global instruction that
"'Standing' or 'implied' permission … is completely forbidden."

I am not auditing the storage-maintenance branches, per my scope; I am recording
that **this text must not reach `main` in this form or on this branch**.

**Fix:** strip it from the sprint worktree entirely. If the rulings are real,
they belong on the storage-maintenance lane with the [USER] text quoted verbatim
and marked relayed, and with the charter it cites *tracked*, reviewed on its own
merits.

### R6 — HIGH — the sprint's single most important state record is untracked, and the tracked records are stale

- `docs/2026-09-06_typed-sprint-pause-state.md` — "**PAUSED BY USER.** … O1–O5
  … All remain mandatory … The goal is neither complete nor declared blocked: it
  was explicitly paused for disk investigation" — is **untracked**. So are
  `docs/2026-09-06_c1-contract-handoff.md` (the charter §4 C1 deliverable),
  `docs/2026-09-06_storage-*.md`, `docs/storage-operations.md`.
- The tracked outcome table, `docs/2026-09-05_typed-consumer-sprint-handoff.md:19–27`,
  is frozen at an early state ("O2 … mixed-store runtime work **started**";
  "O4 … prototype **started** in a separate worktree") while the tail of the same
  file (`:798–847`) records O2 terminal integration accepted. Status line `:10`
  still reads "IN PROGRESS — O1 PUBLIC CONTRACT VALIDATED".
- The plan of record, `docs/2026-09-05_master-plan.md`, gains one stale
  checkpoint (+21 lines) describing only the Boolean storage increment. The §7
  **F2/F3/F5 disposition rows are not updated**, so the substantial F5 answer
  and the F3 route are not recorded against the findings they discharge.
- `docs/2026-09-05_typed-consumer-sprint-handoff.md:832` asserts "The user's
  authorized primary `.tmp` cleanup removed 68,122 files … approximately 14.2
  GiB" — a destructive action attributed to [USER] with no quote, no date, no
  relayed marker, and no entry in the decision ledger at `:29–36` (which still
  reads "No critical issue has yet been identified").

**Fix:** track the pause-state and C1-handoff docs; refresh the O1–O5 outcome
table and status line to the tip; update master-plan §7 F2/F3/F5 rows with what
is now proved and what is not; give the `.tmp` cleanup a proper ledger entry
with the [USER] text or downgrade it to [AGENT].

### R7 — HIGH — the evidence payload is a duplicate of the repository, not an audit trail

**734,510 added lines across 2,159 files** under `docs/evidence/` — versus
**~30,400 lines across 251 files** for everything else on the branch
(GoLean 9,015 / docs-notes 6,505 / baselines 4,929 / Tests 3,222 / tools 2,914 /
spikes 1,673 / scripts 1,420 / Corpus 695). Ratio **24:1**. The largest dirs are
`2026-09-06_r1-production-independent` (96,760 lines / 222 files),
`2026-09-06_typed-preflight` (94,936 / 69),
`2026-09-06_i1-envelope-independent` (49,053 / 107). It includes three full
copies of `tools/nativefrontend/emit.go` and a copy of
`GoLean/GoCore/StateWf.lean`. The repo's own convention (`docs/evidence/<date>_<lane>/`
with gate tails, probe transcripts, structural diffs) is small — the reference
example, `docs/evidence/2026-09-05_project-gate-audit/`, is 10 files.

Detailed manifest in §5 (from the payload investigation). This is a
records-hygiene BLOCKER for the branch as a train step, not for the proofs.

### R8 — MED — `baselines/string-members/` has a doubled path segment

`baselines/string-members/panic-recover/string-members/{controls,equal,…}.json`
— the lane name appears twice. Either a path-construction bug in the member
runner or an unintended nesting. `baselines/` is trusted-surface per `CLAUDE.md`;
its layout should not carry an accident.

### R9 — INFO/LOW — things that are right and should be said

- Axiom hygiene holds; no `sorry`/`native_decide`/`axiom` added; no `partial` in
  `GoLean/GoCore/`.
- `scripts/ci` gains **ten new fail-closed gate steps** (Boolean typing,
  Boolean runtime, recovery typing/storage/setup/control, abort observation,
  recovery terminal, observer transport, declarations, string members), each
  `bad`-ing on non-zero. No gate was weakened or made skippable.
- Four baseline re-pins, each with a full run, a written reason, an evidence
  pointer and an independent-review commit id. The single PASS→non-PASS flip
  (`sync/mutex-unlock-fatal/during-panic-unwind`) **is** on a `Cases:` line
  (`docs/BUGS.md:6252`), as `CLAUDE.md` requires.
- BUG-105/106/107 added; `main` ends at BUG-104; no collision.
- The interface facade correctly *removed* "typed admission" from its
  non-establishment list only after actually establishing it, and kept
  "termination, refusal freedom … generic context laws or Iris adequacy" in it.

---

## 4. Evidence payload — quantified, with a keep/drop manifest

Copy detection was done by **git blob-hash identity** against an index of all
14,534 unique non-evidence blobs across all 2,956 commits — exact, not heuristic.

**Tracked repo bytes: main 53,383,905 → HEAD 169,095,601 = +115,711,696 (+216.8%, a 3.17× repo).**
`docs/evidence/` is **114,156,315 B = 98.66% of all growth** (2,159 files, +734,510
lines, 78 new dirs). Non-evidence additions (~1.55 MB) are proportionate and not
at issue.

### Largest evidence dirs

| dir (`docs/evidence/…`) | files | +lines | bytes |
|---|---:|---:|---:|
| `2026-09-06_typed-preflight` | 69 | 94,936 | **55,658,111** |
| `2026-09-06_string-panic-members` | 127 | 43,075 | 11,159,890 |
| `2026-09-06_r1-production-independent` | 222 | 96,760 | 4,599,107 |
| `2026-09-06_r1-integration` | 38 | 43,787 | 3,866,678 |
| `2026-09-06_uintptr-disposition-independent` | 22 | 34,723 | 3,779,714 |
| `2026-09-06_r1-baseline-independent` | 26 | 36,075 | 3,354,780 |
| `2026-09-06_o2-terminal-integration` | 38 | 45,341 | 3,322,518 |
| `2026-09-06_i1-json-integration` | 32 | 39,690 | 3,322,118 |
| `2026-09-06_recovery-facade-final` | 121 | 36,129 | 3,161,613 |
| `2026-09-06_i1-envelope-independent` | 107 | 49,053 | 2,461,213 |
| …68 further dirs | 1,349 | 215,741 | 19,470,573 |
| **TOTAL** | **2,159** | **734,510** | **114,156,315** |

### What the 2,159 files are

| bucket | files | bytes | % |
|---|---:|---:|---:|
| ARCHIVE (`.tar.gz`) | 36 | 55,864,181 | **48.9%** |
| MACHINE-CAPTURE (tsv/json/jsonl data) | 596 | 24,444,399 | 21.4% |
| MACHINE-CAPTURE (hash manifests/inventories) | 156 | 17,137,581 | 15.0% |
| **SOURCE-COPY-EXACT** (blob-identical to a tracked file) | 345 | 9,877,152 | 8.7% |
| GATE-TAIL / TRANSCRIPT | 640 | 2,895,265 | 2.5% |
| SOURCE-COPY-UNCOMMITTED (candidate trees) | 70 | 2,147,387 | 1.9% |
| PROSE (`.md`) | 100 | 1,167,418 | 1.0% |
| PROBE / FIXTURE (genuinely new) | 107 | 613,869 | 0.5% |
| OTHER | 109 | 9,063 | 0.0% |

Intra-payload duplication alone: **511 redundant blobs = 9,544,045 B**
(`cached-full.tsv` 3×, `full-v3.manifest.tsv` 2×, `bugs-ledger-proposed.md` 2×,
`emit.go` 2×; `uintptr-disposition-independent/{full-manifest,independently-regenerated-manifest}.tsv`
are byte-identical in the *same* dir, and the latter's name asserts independent
regeneration).

### The repo's own convention, and the departure

`docs/evidence/README.md` (on main, **unamended by the branch**) rule 4:

> "**Commit SHA**: for any record where repo state matters (machine runs,
> frontend emits, sweeps), **the exact commit the tree was at**, plus a
> dirty-tree note if it was not clean."

Record the SHA — not copy the tree.

| metric | main | sprint | ratio |
|---|---:|---:|---:|
| evidence bytes | 26,485,321 (80 dirs, 1,424 files) | 114,156,315 (78 dirs, 2,159 files) | **4.31×** |
| sprint evidence vs **whole main repo tracked bytes** | — | 114,156,315 vs 53,383,905 | **2.14×** |
| median dir | 24,949 B | mean 1,463,542 B | **58.7×** main's median |
| largest dir | 10,410,369 B | 55,658,111 B | 2,231× main's median |
| `.tar.gz` in evidence | **0** | **36** (55.86 MB) | new, undocumented practice |

Compliance of the 78 new dirs: **23 have no README at all** (rule 1), including
4 of the 6 largest; 47/55 READMEs omit the toolchain line (rule 3); 51/55 omit
the host note (rule 5); **39/78 (50%) are cited by no tracked doc** (rule 8).

`docs/2026-09-06_disk-growth-review.md` (untracked, 328 lines) does **not**
explain this payload — it is about ignored on-disk scratch, and explicitly notes
"source and Git metadata are small" (`:36`), `.git` at 399 MiB (`:40`). Its one
relevant line is an **open item**, not a policy: "Small sealed evidence bundles
need a separate retention policy" (`:200`). Its prescription for compact evidence
(`:169–172`) is precisely a *manifest*, which is what this payload violates.
`.git` in the primary checkout now measures 462 MB. The storage-maintenance docs
that would set a retention policy are **untracked and absent from 7edc298f** — so
this payload lands *ahead of* the policy it is the largest test case for.

### KEEP / DROP manifest

| disposition | files | bytes | % |
|---|---:|---:|---:|
| **DROP** bulk run-capture archives (>500 KB) | 14 | 54,128,839 | 47.4% |
| **DROP** bulk machine capture (≥100 KB) | 76 | 32,477,535 | 28.5% |
| **DROP** exact copies of tracked files | 345 | 9,877,152 | 8.7% |
| **DROP** intra-payload duplicate blobs | 462 | 8,166,531 | 7.2% |
| **KEEP-TRIM** small archives → unpack/patch | 22 | 1,735,342 | 1.5% |
| **KEEP-TRIM** candidate trees → `git diff` vs base | 53 | 1,346,901 | 1.2% |
| **KEEP** gate tails / transcripts | 414 | 2,507,727 | 2.2% |
| **KEEP** small machine captures (<100 KB) | 569 | 2,589,485 | 2.3% |
| **KEEP** prose reviews | 99 | 743,185 | 0.7% |
| **KEEP** probes / fixtures | 99 | 575,951 | 0.5% |
| **KEEP** other | 6 | 7,667 | 0.0% |

**DROP total: 897 files, 104,650,057 B, 612,328 added lines** — 83.4% of the
payload's lines, 91.7% of its bytes. Payload falls to 9,506,258 B (drop only) or
≈6,732,240 B with the trims: **91.7–94.1% reduction**. Branch repo total falls
from 169,095,601 B (3.17× main) to **64,445,544 B (1.21× main)**.

Concrete globs:
- `docs/evidence/2026-09-06_typed-preflight/{capture-full,coverage-artifacts}.tar.gz`
  + `{capture-full,coverage-artifact,source}-sha256.json` — **54,140,569 B in 5
  files**, regenerable by the commands the dir's own `commands.md` records, at the
  base commit `10fefeb3` its own README names.
- `docs/evidence/*/**.tar.gz` (34 more) — 3,458,954 B.
- `docs/evidence/*/source*/**` (359 files, 7,008,581 B) — 289 blob-identical to
  committed blobs; the rest expressible as one `candidate.patch` per dir. The
  payload already demonstrates the pattern (18 `.patch` files, 154,287 B total).
  `i1-envelope-independent/source-v{1,2}` differ in 5 of 32 files yet store
  `emit.go` (471,051 B) twice in full.
- `docs/evidence/*/{source,full-source,candidate-source}.json` (~6 MB) — sha256
  index of all tracked files, byte-reproducible from the recorded commit.
- `docs/evidence/*/{full,full-v3,latest,cached-full}*.tsv` (~14 MB) — regenerable
  by `scripts/coverage-manifest` / `scripts/diff-coverage`; the pinned form is
  already `baselines/native-full.tsv`.

**Replacement:** one `docs/evidence/<dir>/MANIFEST.tsv` of `sha256␉path␉commit`.
At ~120 B/row that is ≈107 KB for all 897 dropped files — 0.1% of what it replaces.

**Auditability of the DROP set — verified, with two exceptions.** 102 distinct
commit hashes appear in the payload's `provenance.json`/README files and **all 102
resolve to real commits**. 62 of the 64 dirs contributing to DROP record at least
one resolvable hash. Spot-check: `r1-production-independent/source/` matches its
recorded base `620489c9` on 135/180 files, the remainder being the reviewed
candidate delta. **Exceptions:** `docs/evidence/2026-09-06_boolean-promotion-review/`
and `docs/evidence/2026-09-06_observer-mock-review/` record **no resolvable commit
hash at all** — those copies are not provenance-tagged and would not survive the
manifest replacement (finding R11).

### Payload findings

- **R7a — BLOCKER —** `2026-09-06_typed-preflight/{capture-full,coverage-artifacts}.tar.gz`
  + 2 sha256 indices: 44.4 MB of pre-compressed archives, 47% of the payload in
  2 files, committed to permanent history. tar.gz gains only 8.5% under git's
  zlib (26,851,540 → 24,556,920 measured), so **≈51 MB of the 55.9 MB archive
  total is undeletable pack cost forever**, vs 15.8% for the JSON they index.
  Contents are 53,693 + 22,510 per-case differential outputs, 100% regenerable.
  There is no `.gitattributes` and no `.gitignore` archive rule to catch this.
  *Fix:* delete the 4 files; keep README, `commands.md`, gate tails and one
  `MANIFEST.tsv`. If the archives are wanted they belong outside git.
- **R7b — HIGH —** 91.7% of the payload is mechanically regenerable or
  duplicative. Git history is append-only; this is irreversible without a
  history rewrite. *Fix:* apply the manifest before any merge.
- **R10 — HIGH —** 23 of 78 new dirs have no README (rule 1); 39/78 are cited by
  no tracked doc (rule 8). *Fix:* README per dir, or delete the uncited dirs.
- **R11 — MED —** `boolean-promotion-review/` and `observer-mock-review/` carry
  no resolvable commit hash. This is the one place the auditability claim
  genuinely breaks. *Fix:* add the base SHA or drop the dirs.
- **R8 (revised) — MED —** `baselines/string-members/`: the doubled path segment
  is **not** a bug — `tools/string_member_runner.py:154` joins the pin namespace
  `baselines/string-members/` with the corpus id `panic-recover/string-members/equal`;
  the sibling `repanic-same-value-abort.json` has no doubling. It is legitimate
  gate-wired trusted-surface baseline data (`scripts/ci:568`). The **real**
  defect is redundancy: all 9 pins carry a byte-identical 17,970 B
  `apparatus_sources` block (143,760 B = 57% of the dir), only 4 lines differ
  per pin, and any edit to any of 172 semantic-core sources rewrites all 9 —
  a guaranteed conflict on every merge train (cf. "Baseline header conflicts
  every train"). *Fix:* hoist `apparatus_sources` into one file referenced by
  sha256; consider aligning with `baselines/certified/`'s `id//\//__` flattening.
- **R12 — LOW —** `docs/evidence/README.md` was not amended to authorize
  archives, size budgets, or a source-copy prohibition. *Fix:* amend it and add
  a `scripts/ci` size check so this fails closed rather than passing silently.
- **INFO — gate tails are the model.** All 640 `.log/.stdout/.stderr/.exit`
  files are under 100 KB (2,895,265 B, mean 4.5 KB). This part of the payload
  follows the convention exactly.
- **HANDOFF TO AUDITOR A —** `docs/evidence/2026-09-06_i1-envelope-independent/source-v1/tools/nativefrontend/emit.go`
  contains `declarationEntryKey` emissions and a `sealDeclarations(program)` call
  that are **absent from `tools/nativefrontend/emit.go` at 7edc298f** (69 diff
  lines). The independently reviewed candidate differs from what landed; the
  review's conclusions may not bind the merged state.

## 5. Records and provenance

### What is right (verified, not assumed)

- **Where the branch cites a real ruling, it cites it precisely.** R-1 is
  genuine — `docs/2026-08-20_w32-re-envelope-charter.md:3` "SIGNED OFF
  (2026-08-20, Mike): approved with defaults … recorded as user rulings", body
  at `:28-50`, and the `[recovered, repanicked]` collapse is named *inside*
  R-1's own quotiented set. `docs/2026-09-06_string-panic-member-assessment.md:8`
  cites it by line number. G-C1 (`charter:241`) traces to
  `master-plan.md:495`. The C4 split citation in
  `docs/language-coverage-ledger.md:416` is a verbatim carry-over from main.
- **The kickoff quote is reproduced verbatim**, typo included ("standign"),
  `charter.md:53-57`. That is good fidelity.
- **No "Gate A complete" and no stable-pin claim anywhere**, with explicit
  disclaimers at `master-plan.md:1934`, `handoff.md:548`,
  `docs/2026-09-06_boolean-program-contract.md:114`. Charter §6 honoured.
- **BUG numbering and re-pin guards are clean.** BUG-105/106 at the tip, 107
  staged; main ends at 104; no duplicates at HEAD and no collisions across all
  70 local branches. All three `Cases:` lines resolve to real corpus cases.
  `scripts/check-bugs.sh` → **exit 0**, verbatim:
  ```
  check-bugs: ok (107 bug(s); pinned cases behave as claimed)
  check-bugs: backlog — 14 unexplained fidelity failure(s): coverage 10/10; latitude 4/4; wrong-answer 0/0
  check-bugs: 'wrong-answer' is the class that ratchets toward 0; …
  ```
  Both status flips are correctly guarded on a `Cases:` line with a full-run
  header reason. `scripts/ci` changes are purely additive; no gate weakened.
- **I1 shows the best §7 discipline on the branch** — no markers moved, and
  `docs/2026-09-06_i1-admission-design.md:166-178` explicitly refuses to
  pre-empt the descriptor-algebra decision: "That broader Gate A/F11 decision
  remains open independently; I1 should not choose it accidentally … difficulty
  is not authorization for a waiver."

### R13 — BLOCKER — the `uintptr` repair overrides a standing "record it, don't fix it" latitude pin, and un-refuses a refused observation kind, without citing either record

The staged BUG-107 repair is claimed as K3 work
(`docs/2026-09-06_uintptr-identity-repair.md:4`, `docs/BUGS.md:6364` "a separate
K3 fidelity repair"), authorised by the pinned spec's `Type_identity` /
`Method_sets` / `Type_assertions`. The **type-identity** half of that argument is
sound and genuinely K3-eligible. Two standing records say otherwise and are
never mentioned:

- `docs/2026-08-21_w7-desugar-inventory.md:2740` — "**`uintptr` is a gc-pin of
  latitude R1 — record it there rather than 'fix' it.**"
- `docs/2026-08-11_latitude-inventory.md:1766` — inside latitude row R1:
  "`uintptr` (frontend maps to uint64; **observations of it refused**)".

I verified this directly: `docs/2026-09-06_uintptr-identity-repair.md`, the
BUG-107 entry (`docs/BUGS.md:6336-6380`) and the ledger movement
(`docs/language-coverage-ledger.md` §8z-uintptr) contain **zero** references to
`w7-desugar-inventory`, `latitude-inventory`, `J-8`, or "register extension".
The only two files under `docs/evidence/2026-09-06_uintptr-disposition-independent/`
that mention them are `bugs-proposed.md` and `coverage-proposed.md` — i.e. the
whole-file *ledger copies*, not the disposition. The independent disposition
review checks baseline row arithmetic and hashes; it never asks whether a
standing latitude pin was overridden.

Beyond the missing citation, `docs/2026-09-06_uintptr-identity-repair.md:42-45`
records that "The Go observer and Lean observation decoder carry `uintptr`
explicitly, with the pinned unsigned range" — a previously **refused**
observation kind is now emitted. Charter §7 lists "change observation or
terminal policy" as a critical issue; K3 says verbatim "Defer new semantic-policy
choices **and changes to the trusted base**", and the repair edits
`GoLean/NativeToIR.lean` and four `GoLean/GoCore/` modules.

**Fix:** either abort the staged merge and present uintptr as a §7 decision
packet at the closing review, or keep it and add an explicit disposition that
cites and supersedes `w7-desugar-inventory.md:2740`, latitude row R1 and
register extension #6, amends those records, and obtains a **third-lane** review
of the latitude override specifically. Either way BUG-107 must not land as an
uncommitted index state (R1).

### R14 — HIGH — the terminal-classification change was re-framed to avoid §7

The sprint rewrote the oracle's crash-observation channel (new
`tools/coverageharness/{abortkind,crashhook,crashview,observe}.go`, `SetCrashOutput`
in the oracle, scoped `GOTRACEBACK=system`) and flipped a previously-PASS
conformance row to a refusal (`docs/BUGS.md:6310-6316`). The self-applied test
was: "it supplies terminal evidence from the same oracle execution **without
wrapper changes or a semantic-policy change**"
(`handoff.md:246-248`). But charter §7 does not say "semantic policy" — it says
"**change observation or terminal policy**", and what changed is exactly what the
oracle will accept as an authenticated terminal kind, hence the conformance set.
`CLAUDE.md` trusted-surface item 2 is "the coverage runners, the tracked
baselines, the oracle pin".

Stated fairly: the direction is fail-closed (a claim *lost*, not gained); the
flip is on BUG-106's `Cases:` line; a full run and written reason are in the
baseline header; and the forgery counterexample (`print("panic: forged\n\t");
panic("actual")`, `docs/BUGS.md:6300`) is preserved and honest. This is good
work. The defect is that it was adjudicated internally under K3 rather than
frozen and packaged for the closing review.

**Fix:** add BUG-106 and the classifier rewrite to a §7 deferred-critical-issues
table for [USER] ratification. "Endorsed by the root coordinator" is not a
substitute — charter §6 says the implementer cannot waive its own finding, and
root is the integrator.

### R15 — HIGH — the decision ledger is factually false

`docs/2026-09-05_typed-consumer-sprint-handoff.md:29-36` is the *entire* decision
ledger, unchanged since kickoff, and ends:

> "**No critical issue has yet been identified. No additional user decision is
> required to begin the authorized work.**"

`grep -i critical` over all 847 lines returns exactly that one line. Meanwhile
the branch carries at minimum: the BUG-106 terminal-classification flip (R14),
the uintptr latitude override (R13), the R-1 authority re-reading (R3), and a
withdrawn B7 V1 kernel-sharing completeness claim. Charter §7 requires each in
the tracked ledger with reproducer, affected claim, rule, alternatives,
recommendation and cost of deferral. None is there.

**Fix:** replace `:35-36` with an itemised §7 deferred-critical-issues table.
That table *is* the closing decision packet charter §6 requires.

### R16 — HIGH — the only accurate state record is untracked and contradicts the tracked one

`docs/2026-09-06_typed-sprint-pause-state.md` is `??`. It is by a wide margin the
most honest account on the branch, and none of it is in the tip:

- `:3` "**PAUSED BY USER.** Do not resume semantic work or full validation jobs
  merely because storage maintenance finishes." — nothing at the tip records this.
- `:56-58` "The staged baseline is **PROVISIONAL** 3,643 = 3,399 PASS + 244 FAIL,
  an exact three-way union, **not a measured combined full run**" — whereas
  staged `docs/BUGS.md:6358` states the isolated lane's 3,635 = 3,390/245 with no
  union caveat.
- `:63-71` "Root job 13552 was stopped at user pause … actual exit **143** …
  Full/slow did not finish; fresh members did not start. Do not infer success
  from a missing wrapper exit file."
- `:87-89` "The V1 kernel-sharing completeness claim is **withdrawn**."
- `:146-152` "Full CI job 73832 actually exited **1 before pause** … shutdown's
  authoritative handle said **1**."

Also untracked: `docs/2026-09-06_c1-contract-handoff.md` — the C1 deliverable
charter §4 mandates. `CLAUDE.md`: "Capture decisions in tracked files, not chat";
an untracked file is one `git clean` from chat.

**Fix:** commit the pause-state and C1-handoff docs before the landing decision;
fold their qualifications into the outcome table and BUG-107's text.

### R17 — HIGH — six committed whole-file copies of the bug ledger, one carrying a bug number the real ledger lacks

Committed at the tip: `2026-09-06_r1-baseline-independent/bugs-ledger-proposed.md`
(6,334 lines) and `.before` (6,307), `2026-09-06_string-panic-members/bugs-ledger-proposed.md`
(6,334) and `bugs-case-pin-proposed.md` (6,334),
`2026-09-06_uintptr-disposition-independent/bugs-proposed.md` (6,340) — against
`docs/BUGS.md` (6,334). These are whole-file duplicates, not diffs, and `.patch`
files exist alongside that would suffice. Worse, `bugs-proposed.md` contains
`## BUG-107 — uintptr is lowered as uint64 …`, which is **absent from
`docs/BUGS.md` at the tip**. A committed evidence file allocates a bug number the
ledger of record does not carry, and `scripts/check-bugs.sh` does not police
evidence copies.

**Fix:** delete the five copies, keep the `.patch`/`.json` proposals; add a
`check-bugs` assertion that no file outside `docs/BUGS.md` matches `^## BUG-`.

### R18 — MED — [USER] provenance markers are missing throughout

Project convention on main is "[USER] Mike, 2026-09-05, verbatim as relayed by
the [AGENT] coordinator — cite as relayed" (`master-plan.md:19`,
`language-coverage-ledger.md:370`, `CLAUDE.md`). **Zero** of the branch's seven
[USER] citations carry it — `charter.md:3-7`, `:53-57`, `handoff.md:5-9`, `:31`,
`master-plan.md:1920`, `AGENTS.md:8`, `CLAUDE.md` (R4). The kickoff quote is the
most load-bearing citation on the branch and is unmarked.

### R19 — MED — `AGENTS.md:122` tags an [AGENT]-designed deletion lifecycle as [USER]

> "[USER], 2026-09-06: the storage-maintenance charter authorizes the narrow
> lifecycle in `tools/audit_scratch.py` …"

The user's actual words in the cited (untracked) charter are "please write a
short charter for this work, then execute on this" — that authorises the arc,
not a named tool's deletion semantics, which the charter itself labels "[AGENT]
operating choices". Re-tag as "[AGENT], under the [USER]-authorized storage
charter of 2026-09-06". (This is the same uncommitted hunk as R5.)

### R20 — MED — `docs/2026-09-06_b7-context-store-design.md:135` cites a ruling that does not exist

> "A `gc386` fidelity claim is outside this migration and the existing
> host-capability ruling."

Repo-wide there are exactly two `host-capabilit` hits and **both say the decision
is open**: `master-plan.md:1402` "Decision: host capability — a machine-global
matter the [USER] owns"; `docs/assessment/decisions-2026-08-31.md:43` "deferred,
needs a host-capability call". Direction of use is conservative (it *excludes* a
claim), hence MED. *Fix:* "…the host-capability decision remains open and
[USER]-owned (master plan §1402)."

### R21 — MED — the reviewer that raised a finding retracted it in-place in its own sealed artifact

`docs/2026-09-05_typed-contract-design-review.md` is by "[AGENT] independent
reviewer `typed_contract_review`". At `:113-121` it raised the boxing-identity
item and stated "This review does not authorize a new byte observation format or
a reduced profile." The retraction was then written **into the same sealed
artifact** at `:3-8` ("**2026-09-06 corrigendum:** … the boxing discussion below
overstates the need for a new policy decision") and elaborated by the same lane.
Charter §6: "the implementer cannot waive its own finding." Partially cured by
`docs/2026-09-06_string-member-design-review.md`, but the confirming reviewer is
the root integrator — an interested party — and the sealed artifact was edited
rather than annotated by a separate dated disposition.

### R22 — LOW — the R1 re-pin ran outside the recorded resource envelope

`baselines/native-full.tsv` header: "Actual run used 32 workers under the
unchanged 16G cap … This missed earlier lane coordination; future conformance
explicitly uses 2." The recorded envelope is 16 GiB / 3 Lean threads / **2
coverage workers**. Self-disclosed and corrected forward; recorded so the closing
review can confirm the R1 baseline is still acceptable evidence. (Auditor A
raises the same point as its R5.)

### R23 — MED — `docs/2026-09-05_typed-consumer-sprint-handoff.md:832` attributes a 68,122-file deletion to [USER] with no quote

> "The user's authorized primary `.tmp` cleanup removed 68,122 files … approximately
> 14.2 GiB of allocated files."

No quote, no date, no relayed marker, and no corresponding decision-ledger entry
(the ledger still says no critical issue has been identified — R15).
*Fix:* give it a proper ledger entry with the [USER] text, or downgrade to [AGENT].

---

## 6. Landability partition

Coordinated with auditor A, who reports **DO-NOT-LAND** for the semantic/gate
content with a BLOCKER (A-R1) that the `string-member` lane grants PASS on rows
where the machine's text is a known divergence from gc, plus A-R2 (a latitude
choice baked into `renderPanicHead`'s evaluator recursion — the `AGENTS.md`
"no semantic choice hides in evaluator recursion" rule), A-R3 (fail-closed
refusal replaced by a divergent answer), A-R5 (no fresh full-corpus run at the
tip) and A-R7 (the branch is not in a landable state). A's R1/R3 and my R3
converge independently on the same object from different directions — A on the
comparison semantics, me on the ruling's scope.

| # | Component | Disposition | Reason |
|---|---|---|---|
| 1 | **Core proof modules** — `GoLean/GoCore/{Boolean*,Recovery*}.lean` (~40 modules, 8,515 lines), `GoLean/Interface.lean`, `Tests/{Boolean*,Recovery*}.lean`, the ten `lean_lib` globs | **LAND AFTER** (R2 docstring correction) | The strongest work on the branch. Non-vacuous, kernel-checked, allowed axioms only, all-successor preservation over the Prop relation, progress, driver refusal-freedom. Builds clean at the tip (111 jobs, exit 0). Only fix owed: state in `Interface.lean` that both profiles are choice-free so `∀ ch` carries no nondeterminism evidence. |
| 2 | **New `scripts/ci` gate steps + `scripts/check-*` for group 1** | **LAND AFTER** (with group 1) | Ten additive fail-closed steps. Must land with the modules they gate, never before. |
| 3 | **Machine/frontend semantic changes** — `Machine.lean` panic rendering, `PanicText.lean`, `StringPanic.lean`, `AbortObservation.lean`, `renderStringMember`, the ` [recovered]` suffix | **DO NOT LAND** | Auditor A's BLOCKER; my R3. R-1's scope extension and the escape-member envelope question are [USER] decisions under K3/§7, not sprint decisions. |
| 4 | **`uintptr` / BUG-107** (staged, uncommitted) | **DO NOT LAND** as-is → **SPLIT OUT** | R13. Overrides a standing latitude pin without citing it; un-refuses a refused observation kind; touches the trusted surface; exists only as an unresolved merge with a *provisional* union baseline. |
| 5 | **Observer / terminal classification** — `tools/coverageharness/{abortkind,crashhook,crashview,observe}.go`, `GOTRACEBACK=system`, BUG-106 flip | **SPLIT OUT** (own lane) | R14. Fail-closed direction and honest counterexamples, but it is an observation-policy change adjudicated internally under a K3 reading K3's own text excludes. Needs a §7 packet. |
| 6 | **Spikes** — `spikes/iris-customer` (+1,446/−63), `spikes/i1-declarations` | **LAND AS-IS** | Outside the default build graph (verified: no `[[require]]` in the root lakefile; Iris pinned to the F3 revision in the spike lakefiles only; no `GoLean/`→`spikes/` import). Honest README about unfolding internals. |
| 7 | **Corpus + `baselines/string-members/`** | **LAND WITH group 3** | The corpus cases are good; the baselines are the pins for the rendering change and cannot land without the decision on it. Fix R8's `apparatus_sources` redundancy first (a guaranteed conflict every train). |
| 8 | **`baselines/native-full.tsv` re-pins** | **LAND AFTER** re-measurement | Four re-pins, each with a full run and written reason — good practice. But the staged union is **provisional**, the tip has no fresh full run (A-R5), and R22's 32-worker run needs confirmation. Merge-protocol 5a also requires `--slow` because `NativeToIR.lean` is touched. |
| 9 | **Python tools** — `tools/*-audit.py`, `tools/string_member*.py`, `scripts/check-observer-*.py` | **LAND WITH their gates** | Untrusted tooling; harmless. But 47 of them are *unstaged* in this worktree (R1) — the committed versions are not what ran. |
| 10 | **Docs / design notes** (43 files, 6,505 lines) | **LAND AFTER** (R15, R16, R18, R20, R21) | Genuinely good analysis. Owed: a real §7 ledger, the untracked pause-state and C1 handoff tracked, relay markers, the phantom host-capability ruling corrected. |
| 11 | **`docs/evidence/**`** (2,159 files, 734,510 lines, 114 MB) | **DO NOT LAND** as-is | R7a/R7b/R10/R11. Apply the §4 manifest: drop 897 files / 104,650,057 B / 612,328 lines; keep ~9.5 MB. Git history is append-only — this is the one decision that cannot be undone later. |
| 12 | **`CLAUDE.md` edit** | **DO NOT LAND** as written | R4. Retitling the merge protocol "to main" scopes gate-green and the audit ask off feature merges; K4 spoke only to approval. |
| 13 | **`AGENTS.md` committed hunk** (sprint pointer) | **LAND AS-IS** | A pointer addition; fine. |
| 14 | **`AGENTS.md` uncommitted hunk** (Retired Worktrees / storage) | **DO NOT LAND** | R5/R19. A standing approval for destructive deletion, from a paraphrase, contradicting `AGENTS.md`'s own rule three lines above and the user's global prohibition on standing permission. Belongs on the storage lane, with verbatim [USER] text, or nowhere. |

### Recommended landing order — four branches

**Prerequisite (blocking, before any branch is cut):** resolve R1. Complete or
abort the staged `5f185fb3` merge as its own commit; evict every
storage-maintenance edit from this worktree; reach a clean tree at a named
commit; re-run `scripts/ci --diff` there. Nothing below is reviewable until the
tip is the artifact.

1. **`typed-contract-core`** — components 1, 2, 6, and the group-10 docs that
   describe them. Plus the R2 docstring fix and the corrected `AGENTS.md`
   pointer. *Audit ask:* vacuity and false uses of the exported theorems; that
   the profiles' stated smallness matches their grammars; that the ten new gate
   steps fail closed. **This is the branch worth landing, and it should land first
   and alone.**
2. **`typed-records`** — the §4 evidence manifest (drop 897 files), the §7
   decision ledger (R15), the tracked pause-state and C1 handoff (R16), relay
   markers (R18), R17's ledger copies, R20's phantom ruling, the reverted
   `CLAUDE.md` (R4). *Audit ask:* that every [USER] assertion traces to K1–K5 or
   a pre-existing ruling and is marked relayed; that no ledger copy survives.
3. **`typed-observer-terminal`** — component 5, carrying its own §7 decision
   packet. *Audit ask:* whether the oracle-authentication change is an
   observation-policy change requiring [USER] ratification; A-R6's silent
   degradation to the raw fallback.
4. **`typed-rendering`** and **`typed-uintptr`** — components 3, 4, 7, 8. Both
   are [USER] decisions, not agent decisions. *Audit ask:* for rendering, does
   R-1 extend to explicit-string payloads including a non-Go-producible escape
   member; for uintptr, does the `Type_identity` argument supersede latitude row
   R1 and `w7-desugar-inventory` J-8, and is un-refusing the observation kind
   in scope. Neither should land before the closing review answers them.

Do **not** land this as one train step. The proof work is being held hostage by
an unresolved merge, a 114 MB payload, and two latitude decisions that belong to
the user.

### One correction to the framing of this review

The branch is not a completed sprint awaiting a landing decision. Its own
untracked record says: "**PAUSED BY USER** … O1–O5 … All remain mandatory … The
goal is neither complete nor declared blocked: it was explicitly paused for disk
investigation" (`docs/2026-09-06_typed-sprint-pause-state.md:3,14-20`). O4 (B7)
is not implemented — `grep ProgramCtx GoLean/` returns one comment in
`Platform.lean:19` saying it is deferred. O5 is `Pending`. Charter §6 forbids
turning a deferred obligation into a completed one by changing its label; the
sprint has not done that, and the closing review should not either.
