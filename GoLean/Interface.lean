import GoLean.GoCore.Trace
import GoLean.GoCore.PoolTrace
import GoLean.GoCore.ProgramTrace
import GoLean.GoCore.Admission

/-!
# Experimental semantic consumer interface

Import this module for `GoLean.Semantics`' choice-labelled sequential trace,
detector-checked pool trace, complete program-driver bridge and observations.
It has no dependency on Iris, the frontend, or either customer package.

* `iter_iff_trace` describes exactly `n` successful steps at a fixed stream.
* `run_ok_iff` relates sequential success to a trace bounded by the supplied
  fuel, retaining both initial and residual choices. `Trace.erase` yields
  unlabelled `Steps`; no converse to erasure is supplied.
* `Pool.run_iff` includes detector state, main-exit choices, output prefixes,
  terminal outcomes, refusals and fuel exhaustion for the current driver.
* `Pool.program_run_iff` includes executable setup and result-cell readout.
* `Pool.observation_iff` quantifies fuel and choices on both sides and keeps
  normal readout or terminal output. Refusal and exhaustion are not observations.

These are correspondence theorems about the current machine. They do not
establish Go frontend correctness, typed admission, termination, refusal
freedom, scheduler completeness, generic context laws or Iris adequacy.

The separate opt-in `GoCore.Admission.checkBoolean` API checks exactly
`IndexStructure ∧ Entry ∧ BooleanSyntax`, as proved by `checkBoolean_iff`.
It checks all syntactic type indices, Boolean entry arguments, and every
function body against the small Boolean syntax policy. It is not invoked
automatically by the frontend or drivers. It does not check lexical typing,
definite return, general name validity, method-set/display metadata, or
typed runtime states. An admitted unbound-variable program can still refuse;
the core regression suite proves this boundary. The A2 recovery program is
outside this first profile. There is no general `Accepted` guarantee here.

The underlying `GoCore` and `GoCore.Machine` types remain representation
dependent. This facade is experimental: B7, C1 and the composition work may
change that representation. A customer must state any stronger domain and
observation assumptions explicitly. See the dated interface design note.
-/
