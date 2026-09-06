# Independent review: actual-driver abort records

[AGENT] root integrator, 2026-09-06. **Bounded PASS** for the ten exact
inputs in `evidence/2026-09-06_abort-observation-independent/candidate-sources.sha256`.
The runtime/customer author is separate from this reviewer. No O2 completion,
Go fidelity certificate, or broader terminal-policy change is approved here.

The four semantic modules provide exact, all-input erasure to the shipped
sequential and pool drivers. The pool construction uses the existing
pre-fuel classification, scheduler step, detector update and event-output
fold. Its witness records an actual selected abort transition, exact prefix
and suffix, choices, detector states, output and the fuel partition. The
program wrapper includes actual setup and result-location readout. Neither
an alternate sequential replay nor a desired future result is an assumption
in the erasure theorems. Witness extraction is conditional on computed
metadata; it does not assert every program produces metadata.

The complete nonempty chain consists of explicit boxed strings. Invalid
UTF-8 bytes, bytes after LF, chain order and recovered flags survive. An
integer rendering as the same text is insufficient; a nonstring tail also
prevents extraction. `stepAbortRecord?_some` alone describes a local query;
consumers must retain the witness's actual `stepMulti` premise. A forged
event value supplied directly to that helper establishes no execution.

I freshly elaborated the six new semantic/test modules in a separate
worktree at `99e0225d`, using previously compiled base dependencies whose
inventoried sources match the reviewed base. All six elaborations passed.
This is not a fresh build of the entire base. The independent probe module
then passed ten additional kernel-checked statements, followed by the
post-import audit: 43 required theorems, 14,549 imported/local constants,
only the existing foundational axiom allowance.

The probes cover nonempty records, positive step budget, exclusion of a
successful result, detector-failure refusal, integer/string ambiguity,
nonstring tail refusal, exact real-driver output `[255, 0, 10, 65]`, its
actual program/pool witness, sequential terminal-before-fuel behavior, and
an empty pool's explicit missing-main refusal. My first probe version
incorrectly expected an empty pool to terminate normally and referenced
nonexistent helper names; its failed log is retained. Reading `Pool.front`
corrected that reviewer expectation. No implementation was changed to pass it.

The author's source-bound dedicated gate also passed its 21 kernel controls
and six compiled unused-declaration injections. Ordinary CI passed with its
original explicitly cached 3,607/394 corpus records. Those are supporting
author evidence, not an independent full differential run. The exact source
and dependency manifests were rechecked after the independent probes.

Integration conditions and remaining limits:

- Keep checked and broader wrappers distinct. Integer CLI arguments retain
  their actual integer type; nullary typed fixtures do not justify coercing
  an integer into a Boolean argument.
- Setup failures, preexisting tombstones, zero-fuel step frontiers and
  renderer failures need not carry an abort record. Broader certificates
  must refuse when their mandatory actual-driver witness is unavailable.
- The typed completeness statement remains conditional on an actual panic
  result. Full typed refusal exclusion and normal/panic/fuel classification
  remain required O2 work, alongside the shared Iris customer closure.
- The record proves a model execution fact. Source-bound Go controls and
  the separately reviewed R1 renderer/membership argument must establish
  the fidelity claim. A string head with arbitrary tail kinds is insufficient.
- Preserve all existing CI hooks when integrating the additive observer
  hook and target. Final runtime integration gates remain owed.

Reproduction: create a separate checkout of `99e0225d`, install the ten
archived inputs from the evidence directory's `source/` subtree and verify
`candidate-sources.sha256`. Run
`GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped bash scripts/check-abort-observation`.
Then run the archived `Probes.lean` using capped `lake env lean` with a
180-second timeout. The evidence contains all six independent elaboration
logs, both probe logs, original author gate/CI logs, source copies and
provenance. `SHA256SUMS` seals the package; the separate `compile.py` records
the fresh module elaboration procedure used for this review.
