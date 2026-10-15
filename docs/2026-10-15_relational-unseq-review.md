# Independent U1 review

Fresh reviewer `u1_review`, no inherited implementation conversation, 2026-10-15.
The brief named the charter, lane and baseline; scope was unrestricted. Review
was read-only, including independent Lean checks under `LEAN_NUM_THREADS=2`
and `capped`. The reviewer deleted its disposable scratch. The final source
identity and validation follow-up are recorded below.

## Reviewer report

> Independent review of the U1 working candidate found one issue, now fixed.
>
> 1. **R1 — observation hook over-quantified silence (medium; fixed).**
> `SafeUntil.observe` required silence for unrelated transitions satisfying
> `Domain.FrameStep`. I compiled a counterexample using the actual
> `Step.frameFall`: it preserves the heap invariant but emits a normal-return
> observation. The added `SafeUntil.observe_prefix` restricts the requirement
> to reachable, pre-boundary transitions. I reviewed its proof and independently
> compiled the updated module warning-free.
>
> No further semantic correctness findings in the seven new modules, facade
> additions, symbolic source graph or controls. The general proof establishes
> actual all-successor safety and progress, preserves occurrence steps and
> ordered labels, handles entry allocation, and supplies canonical completion.
> Independence is established over all relevant intermediate heaps; it is not
> an assumed permutation law.
>
> **Acceptance remains open:** compiled RD8 compatibility, actual
> projection-specific silence, final CI and exact kernel replay were not
> completed during this review. The 16 inherited implementation findings remain
> unwaived. This review does not establish full U1 completion, concurrent
> transport or arbitrary interleaving equivalence.
>
> My private review scratch was deleted. No tracked files, peer trees or runtime
> code were modified.

## Disposition

R1 is fixed by `SafeUntil.observe_prefix` in `RelationalSegment.lean`, with
`SegmentPrefix.append` retaining the actual path. The proof handles a reached
boundary immediately, so it does not demand silence after completion. The
original uniform observation law remains useful where its stronger premise
holds. [AGENT] 2026-10-15: add this reachable-step hook rather than strengthening
the memory invariant into an unrelated global control restriction.

The counterexample uses `.next (.frame [] [] [] [] .stop fid)` and the actual
`Step.frameFall` to `.next .stop`. Both have the same store and satisfy the
heap-only frame relation, while a normal-return observer distinguishes the
step. This is a failure of the original hook's usefulness for that observer,
not a false theorem or a claim that the source sweep performs a return.

The inherited 16 findings retain their individual open dispositions in the
I1 integration stage table, as stated in the U1 stage. No review finding or
acceptance gap is waived by the kernel-axiom check.

## Fresh RD8 review

A second fresh reviewer, `u1_rd8_review`, received no implementation conversation
and no earlier verdict. The brief pointed at the charter, immutable relay and
candidate paths; scope was unrestricted. Its report, condensed (2026-10-15):

> No new semantic correctness finding in the restricted general theorem or RD8
> adapter. The exact frozen SimulationLaw and GuardedTarget close without a law
> hypothesis. The adapter genuinely consumes Ranked.traversal and source paths;
> interpret recursively consumes every ready branch and those paths, plus
> scheduler_cover, binder_effect and completion_path. This is substantive proof
> dependence, not an unused reference or enumeration of fixture schedules.
> Entry allocation, intermediate admission/safety, actual labels and guarded
> steps remain explicit.
>
> Findings: documentation still says RD8 is pending; and five additional inherited
> implementation findings in frozen Ownership/Source, giving FAIL: 21 combined
> findings. No new U1 declaration finding. Standard axioms do not waive them.
>
> Independent checks: re-elaborated all ten new public modules and the three
> adapter proof modules warning-free; replayed precisely those thirteen modules;
> exhaustively checked 24,953 imported project declarations (standard axioms only);
> checked eight direct proof-body dependencies; verified all 115 frozen Lean
> sources byte-for-byte against eba7d3b; independently ran the fresh alias control
> (exact {-2,7}, eight leaves, certificate 226 nodes/231 edges). No whole-closure
> replay or final CI was repeated by the reviewer. No concurrent atomicity or
> interference stability follows. Reviewer scratch was deleted; no tracked or
> peer files changed.

### Findings and dispositions, one by one

1. **Stale pending-status documentation — fixed.** The stage, facade reference,
   original package README and new adapter README now record the exact RD8 pin,
   closed results, dependency mapping, reproduction and remaining limits.
2. **pathTags_persistent._unsafe_rec — raised, open/unwaived.** Full name
   `GoLean.IrisCustomer.pathTags_persistent._unsafe_rec`; frozen
   `GoLeanIris/Ownership.lean:596`. It is reported separately from standard axioms.
3. **ScalarTy renderer 1 — raised, open/unwaived.** Full name
   `GoLean.Logic.Source.instReprScalarTy.repr_1._unsafe_rec`; frozen
   `GoLeanIris/Logic/Source.lean:93`.
4. **ScalarTy renderer 2 — raised, open/unwaived.** Full name
   `GoLean.Logic.Source.instReprScalarTy.repr_2._unsafe_rec`; same frozen source.
5. **FieldTys renderer 1 — raised, open/unwaived.** Full name
   `GoLean.Logic.Source.instReprFieldTys.repr_1._unsafe_rec`; frozen
   `GoLeanIris/Logic/Source.lean:99`.
6. **FieldTys renderer 2 — raised, open/unwaived.** Full name
   `GoLean.Logic.Source.instReprFieldTys.repr_2._unsafe_rec`; same frozen source.

These five do not replace the sixteen individual upstream dispositions in the
I1 table. All 21 remain failures, not waived or converted into partial passes.
The frozen Memory warning and live logic `35 NOT-PUBLIC` result remain visible.

The reviewed adapter source hashes were:

- Base.lean: fe98731d06ed8db99ef085517fd7e28037eeb86192eb96ccdf5a26ebcbef0138
- Source.lean: a7598de8410eb5c15827edcc03d3446bbe6a93a82ed8fa4a43a3f2d375179ae5
- Simulation.lean: 8ea574612a6c88398e9e07e93fdf98f63d10f6c9adcb2a05770ec6bb3da6f180

## Author validation

- Full `scripts/ci --diff` passed on the earlier dirty U1 tree: 4,025/4,025
  differential rows and 415/415 negative rows, no baseline regressions; all
  speedbumps green. Existing expected corpus failures remain in the baseline.
  This run preceded the final traversal/adapter additions and is not advertised
  as a final-commit differential run.
- Final warm root build passed, 246 jobs, warning-free; final `scripts/ci` passed
  in 160 seconds with 106 exact GoLean modules kernel-replayed (57.68 seconds,
  peak 5,036 MB), core totality, evaluator, frontend and other gates green.
  Speedbumps green. Runtime, detector, frontend and drivers are byte-identical to
  I1; only proof modules/facade and experimental files/docs changed, so no new
  operational equivalence theorem is needed or claimed from those finite tests.
- U1 package build passed (75 jobs); exhaustive selected closure: 19,610
  declarations, standard axioms only; implementation scan FAIL, inherited 16.
- Frozen RD8 adapter build passed (326 jobs, only the inherited Memory warning);
  exhaustive selected closure: 24,960 declarations, standard axioms only;
  implementation scan FAIL, inherited 21. Six direct proof-body reports cover
  all links in the stage mapping. All four original frozen inputs are unchanged.
- The unchanged I1 ProgramOutcomeConstraint compiled against the final facade;
  its four headline laws use standard axioms only.
- D1 package rebuild passed (89 jobs), retaining both positive pool executions,
  comparator/shadow laws and unconditional pre-pair rejection. Its exhaustive
  selected closure is 22,022 declarations, standard axioms only; implementation
  scan FAIL, inherited 16. DetectorControls also executed successfully; its dump
  is not an additional equivalence proof.
- Fresh alias source control passed independently and in author validation.

- Normal replay passed for exactly U1's three modules, Concurrency's eight
  modules, and the adapter's four modules. Fresh replay of U1.Audit,
  Concurrency.Audit and U1RD8.Audit each returned exit 0, reconstructing the
  respective entire imported environment from empty, including dependencies.
  The I1 standalone constraint module also replayed successfully. These are
  completed checks, not inferred from build success.
- Reviewed adapter hashes match the final source exactly. Frozen logic files
  are unchanged. Historical concurrency f6f37e36f4844d7e3730496a4fa23b48e5a48e0e
  and D1 b4282cffc19dbb092c3c54bd83d56996a808ba45 remain in their own trees.

The branch contains no operational/public-runtime changes, main merge, push,
live repin, peer writes or global changes. The source worktree is retained;
private dependency copies, caches, builds and logs are deleted after checks.
The immutable implementation identifier is recorded in the subsequent handoff
commit, which changes documentation only.


## Immutable handoff

Implementation: **82a2ff3139053c2a23d97cc90d8f21bb2400d96f**.
Base: **5d8e53e9f1a046fb645fce49901de714591e0819**.
Branch: `spike/relational-unseq-1015`.
Source worktree: `/home/mike/projects/golean/.claude/worktrees/relational-unseq-1015`.
This follow-up commit contains only this review/handoff update; the checked
implementation and reviewed proof hashes are unchanged.

The independent reviewer rechecked the documentation disposition after the
implementation commit: "Documentation finding is fixed." It confirmed the
summary faithfully distinguishes author validation from independent review and
retains all five additional implementation findings individually open/unwaived.
No further correction was requested.

The first restricted U1 candidate now includes the general theorem, symbolic
source instance, exact frozen RD8 semantic law and original closed guarded
target. The alias behavior set remains distinct. This is ready for the user to
relay to logic for downstream uptake; it neither merges nor repins their tree.
The implementation scans remain FAIL (16 public / 21 combined); the inherited
live logic failure and richer-interface obligations are not closed by this
candidate. O1 is independent and unchanged.

Cleanup completed in this lane only: root `.lake`, `.tmp`, `deps`, `artifacts`
and the two local experiment `.lake` directories and untracked manifests were
removed (about 11.5 GB total). No source, tracked manifest, historical worktree,
peer build state or shared cache was removed. Reconstruct using the stage and
adapter README commands; no disposable evidence dump is committed.
