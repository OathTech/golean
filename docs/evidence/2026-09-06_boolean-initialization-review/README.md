# Independent exact Boolean initialization review

[AGENT], 2026-09-06; reviewer `typed-preflight`, independently of the
implementation lane. **PASS within the exact-initialization scope; no
blocking source finding.** This verdict does not accept the separate runtime
invariant or declare O1 complete.

The reviewed frozen source is the uncommitted `BooleanInitialization.lean`
increment over integration revision
`8b0a6a227c1bc50a1768f0c503e94e21c3b14790`, including appended paired
regressions and facade/interface-audit changes. `provenance.json` binds those
bytes, relevant underlying helpers and the completed interface gate log.
All writes and independent probes were confined to this reviewer's worktree.

## Assessment of the actual claims

`declareRoots` describes successive calls to the actual environment
declaration operation, with monotonically increasing addresses. Its lookup
theorem requires distinct newly declared names; preservation of absent old
names makes the relevant shadowing obligation explicit. The exact binder and
allocator equations are proved against the existing helpers, including the
base cases, supplied Boolean values and false defaults. They append cells
to the prior heap without claiming the prior heap or environment was typed.

The canonical initial environment declares arguments followed by results.
Its stored association-list order is reversed, while heap order and the
lookup lemmas retain the original argument/result indices. `initialState`
stores the supplied values followed by exactly the result-count false cells.
The argument read lemma is bounded by the actual supplied value list; the
result read lemma additionally requires its length to equal the function's
argument count. These are essential distinctions, not incidental proof
arguments.

`initialResults_distinct` holds for the canonical arithmetic list even for a
malformed function. Identification of that list with actual driver pins
requires distinct signature bindings. `setup_typed_exact` obtains those
bindings from the stronger admission/`FunctionTyped`, and proves the real
`runProgramSetupM` equation. Thus its distinct actual pins are justified;
unconditional distinctness is not being asserted for A3a's duplicate-name
counterexample. Exact offsets also suffice to distinguish argument roots
from result roots by their respective bounds.

The setup proof derives the actual binder/allocator/pin equations, preserves
the whole program context, and transports the earlier derived typed-storage
facts through equality of the actual setup results. It does not assume setup
success or future execution as a premise. `booleanEntry_wf` derives the
existing `MachineWf` obligations from all environment roots, Boolean cells,
the admitted body and its actual empty driver barrier. Result pins remain
external to that barrier, matching the driver's implementation.

Arbitrary setup fuel, including zero, and an unchanged arbitrary choice stream
are valid for this profile because globals/package initialization are
excluded and Boolean binding/default allocation performs no execution or
choice consumption. These are facts about the existing finite-array model,
which has no explicit root-allocation quota, not a guarantee about unlimited
physical memory. No termination, reachable control typing, preservation or
Iris-resource theorem is claimed by this increment.

The `initialEnv_*`/`initialState_*` lemmas describe canonical objects. To treat
them as facts about an actual program invocation, a consumer must first use
the setup equation and its admission/arity premises. The new facade follows
that distinction; the earlier helper ledger remains historical evidence for
its weaker increment.

The new `docs/2026-09-06_boolean-initialization.md` claim ledger was also
reviewed and matches these limits. It explicitly separates canonical objects
from actual setup, makes the result-offset length premise visible, preserves
the weak-admission alias counterexample, and identifies execution safety and
Iris ownership as subsequent obligations. Its exact bytes are included in
the source provenance. References to preserving existing bindings concern
stored binding occurrences; a new declaration may shadow their visible lookup,
as `declareRoots_lookup_absent` and the retained counterexamples show.

## Independent checks

`Adversarial.lean` freshly elaborates eight theorems against the integration
build's read-only imports. The exact command is in `provenance.json`; it uses
`scripts/capped`, 16 GiB and three Lean threads, without requesting any output
`.olean`. `probes.log` and `.exit` record success. All probe dependencies and
`setup_typed_exact` itself use only the classical trio.

- Two generic consumers combine named lookup with the exact argument value
  or result zero at that same location. Names, program, function, values and
  index are parameters; no generated-name convention or fixture identity is
  used.
- A duplicate-name function has a distinct canonical result list but actual
  aliased pins. The stronger checker rejects it, preventing application of
  the actual-setup claim to that counterexample.
- A mismatched argument count makes a canonical result offset load `true`.
  This challenges dropping the length premise from the result-zero lemma.
- The exact binder appends `[false, true]` after a malformed existing cell and
  a hidden dangling binding. It retains both defects, and the resulting heap
  remains untyped. This challenges interpreting exact helper success as
  unconditional state repair.

The appended paired regression independently reduces the actual driver for
all four two-argument Boolean combinations, arbitrary fuel and choices, with
two different result roots and an empty frame. Its admission witness and
result-zero API use complement the generic theorems.

The interface gate passed with **41 required exports, 11,879 audited
constants, and seven compiled poison rejections**, including an unused private
axiom in `BooleanInitialization`. Fresh elaboration includes the new module;
the post-import origin sweep includes all imported local declarations. The
completed gate log is retained here. Ordinary CI was also inspected as PASS:
202 fresh eval checks, with the full executable and negative records explicitly
cached from `10fefeb3`. The reviewer did not rerun the full corpus for this
proof-only change.

The remaining integration must compose exact setup with the independently
reviewed `Inv` and its actual driver safety/readout theorems, then expose and
gate that composed contract. B7 implementation remains downstream of that
checkpoint. Check `SHA256SUMS` before consuming this report.
