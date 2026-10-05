-- This module serves as the root of the `GoLean` library.
-- Import modules here that should be built as part of the library.
import GoLean.StrictJson
import GoLean.GoCore
-- The relational trace/run correspondence, the abort observer and the string-panic
-- members reached the default build only through the parked facade GoLean.Interface
-- (docs/2026-09-16_typed-profiles-parked.md §3); they are core and are wired here
-- directly so nothing leaves the build silently. ProgramTrace pulls PoolTrace;
-- AbortObservation pulls Trace.
import GoLean.GoCore.ProgramTrace
import GoLean.GoCore.AbortObservation
import GoLean.GoCore.StringPanic
-- The window's contract (charter row 0; packet A, 2026-09-27): the pinned stable bridge set
-- (a statement drift fails THIS build) and the execution statement (Prop definitions only;
-- packet B proves them). Enrolled here = default-build membership.
import GoLean.GoCore.BridgeSet
import GoLean.GoCore.ExecutionStatement
import GoLean.GoCore.Prefix
-- Window packet D (2026-10-03): the per-arm `stepFn` EQUATIONS with the `stepFn_eqns` rewrite
-- set (charter row 7's second check) and the sequential-to-pool PROJECTIONS (packet B audit F5).
import GoLean.GoCore.EquationsAttr
import GoLean.GoCore.Equations
import GoLean.GoCore.PoolProjection
-- The pool/registry half's SPEC PACKET (design gate, 2026-10-04): the labelled pool relation's
-- frozen DEFINITIONS and its target STATEMENTS (Prop definitions only; the grind proves them).
-- Enrolled here = default-build membership and the core audit's two-way closure.
import GoLean.GoCore.PoolStep
import GoLean.GoCore.PoolStatement
import GoLean.GoCore.PoolErrorFacts
import GoLean.GoCore.PoolReplayFacts
import GoLean.GoCore.PoolSound
import GoLean.NativeToIR
import GoLean.CLI
import GoLean.ChoiceTrace
