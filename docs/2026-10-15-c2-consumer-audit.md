# RD6/C2 consumer integration: independent result review

Reviewed upstream implementation: `626faca5a26f57fbf367aa9655e2aef08f20143a`.
Frozen logic implementation: `bbb372e2b97eec663f55a01ee4993f98be829e1b`;
reviewed logic handoff: `e584674d3b62042c5f082318dc8332ab96593b47`.
Review date: 2026-10-15. The reviewer read the RD6/C2 relay and C2 charter,
inspected the phase carriers, coverage/realization and their dependencies, the
actual setup/program drivers, the frozen request, the consumers and the original
program target. This review formed its own conclusions; prior review verdicts
were not used as proof evidence.

**Result: no blocking finding or concrete follow-up defect in this integration.**
The exact semantic request is discharged. The original program acceptance
remains conditional on downstream `InitAssembly`; this is not a closed Iris
whole-program adequacy result or live migration.

## Semantic and consumer assessment

`ProgramExecution.Correspondence.phase_projection` has exactly the supplied
`RelationalCodeX.C2.ProgramPhases` type, checked by direct theorem assignment.
It preserves the original input tape, uses each full phase fuel budget, and
composes initialization, main execution and fallible readback by the actual
`Except` bindings. Initializer errors are already wrapped by `runPkgInitM`;
body/readback errors propagate unchanged. Normal readout keeps empty output.
The proof uses the general checked validation, seeding and activation views
and `setup_eq`. Its seed equation derives the driver's actual validity check;
it adds no external well-formedness, successful-init or no-refusal premise.
The total activation premise is precisely the frozen request's premise.

This corollary does not replace or restrict unrestricted `Coverage`: arbitrary
program, arguments, fuel and tape remain quantified without safety hypotheses.
The independent semantic carriers retain ordered failure phases and segment
histories; the bridge's tapes do not define those carriers. The corollary is a
checked program boundary equation, not a new per-evaluator-arm API.

The frozen `entry_ready` derives activation for all stores from the original
`Definition`/`ValuesTyped` evidence. Captures are concatenated to supplied
arguments and result roots start after the actual arbitrary initialized heap
base and argument cells. The frozen consumer preserves those inputs, its
observer and actual history witnesses. `InitInvocation` is reused unchanged.

`C2Acceptance.programAcceptance` supplies the semantic law while retaining
`assembly : InitAssembly`. I independently extracted the complete original
`closed_program_init_outcomes` header from logic commit
`14cef5e62c7b42a1e0e1eae3a12c2d8674968c01`, added that explicit assembly
argument, and proved the unchanged header using the new acceptance, including
its original `FS` argument. It compiles and replays. No old executable adequacy
proof or weakened target is substituted.

## Independent validation

All heavy commands used `LEAN_NUM_THREADS=2`, `capped`, and a `TMPDIR` inside
this lane. Reviewer outputs were confined to `.tmp/c2-consumer-review`; the
private author package and peer worktrees were read-only to the reviewer.

- Compared all 106 frozen package inputs directly with the immutable logic git
  objects. Only private `lakefile.toml` and `pins.json` differ, for local
  dependencies and the new pin. All original Lean sources are byte-identical.
- Independently rebuilt the updated upstream soundness module, frozen
  `ProgramRequests`, exact adapter, frozen `ProgramConditional`, and full
  acceptance wrapper into separate output paths. All passed without warnings.
- The acceptance's exhaustive local axiom audit checked **5,943 declarations**:
  only `propext`, `Classical.choice` and `Quot.sound`. Headline phase, invocation,
  phase-consumer, conditional-program and original-header acceptance checks
  likewise report only those standard axioms.
- Exact kernel replay passed for these six independently rebuilt modules:
  `GoLean.GoCore.RelationalProgramOutcomeSound`,
  `RelationalCodeX.ProgramRequests`, `RelationalCodeX.ProgramConditional`,
  `C2Adapter`, `C2Acceptance`, and `OriginalAcceptance`. All six expected names
  appeared once and the checker exited zero.
- New upstream and adapter sources contain no `sorry`, custom axiom,
  `native_decide`, `unsafe`, `implemented_by`, extern declaration or disabled
  kernel checking.

The reviewer used built, read-only imports from the author's checked private
package for downstream dependencies, and independently rebuilt the modules
listed above. This is not a claim of an independent full dependency rebuild,
full CI/differential rerun or fresh live gate. The inherited Memory warning and
recorded live **35 NOT-PUBLIC** failure are not discharged by this review.

Reproduce from a prepared private frozen package: build the aggregate plus
`C2Adapter` and `C2Acceptance`, compile their sources with separate `-o` outputs,
and run the pinned toolchain's `leanchecker --verbose` over the exact module
list above with those output paths first in `LEAN_PATH`. For original-header
acceptance, extract text after `theorem closed_program_init_outcomes ` and
before ` := by` from `git show 14cef5e:packages/golean-iris/GoLeanIris/Logic/InitProgram.lean`;
place it in its original namespace, add `(assembly : InitAssembly)`, and apply
`C2Acceptance.programAcceptance assembly GF (FS := FS) O` followed by the
remaining original arguments. Use the same cap, two-thread setting and local
scratch directory. Upstream source rebuild command:

```sh
LEAN_NUM_THREADS=2 TMPDIR="$PWD/.tmp/c2-consumer-review/tmp" capped lake env lean \
  -o .tmp/c2-consumer-review/GoLean/GoCore/RelationalProgramOutcomeSound.olean \
  GoLean/GoCore/RelationalProgramOutcomeSound.lean
```

## Reviewed hashes

- Upstream soundness module: `4515e5bb24cd3fec053843dbafd741cfd395887e93f818dd3459317caa69629e`.
  Independently rebuilt source matches the committed blob at `626faca5`.
- ProgramRequests: `b0c77eebeff8a50e2a597fb5b8ebe218d98580100bdaeb5a2f5301ba06ab9a91`.
- ProgramConditional: `a3f9c2579768f6f1049399ff5d9ff846294ebf528311b39b4934c4e6226857c7`.
- ProgramFrozen: `d9db7e3e008a1e455e9620e033a5152c80bd7acee0c55dc55b4647a926aeaeab`.
- C2Adapter: `82ea637074d4658606d09feeef3edd6e1462077d051ad3d6ba64adb939f1d202`.
- C2Acceptance: `91763f56a009c5df26b751327924339951fda514211ee11f92a32aabca1bda0f`.
- Original program theorem header: `9977c1891dcee16c675546265f9a411ed4adedc666b676fb34e537032f82ccec`.

No findings require disposition. Remaining scope is explicit: downstream Iris
initialization assembly is unfinished; observer census completeness, full
observed adequacy, concurrency and live migration are not established here.
The C2 component readback control does not prove whole-program reachability of
an invalid result location; its general correspondence nevertheless retains
fallible readback without a safety assumption.


After this review, the reviewer also inspected the committed reproduction
recipe: its three Lean clients match the independently checked sources, and
its setup paths, module roots and replay count are consistent. That was a
recipe review, not an additional dependency rebuild. The author's separate
full replay checked 399 modules exactly; it is recorded in the stage, not
attributed to this reviewer.
