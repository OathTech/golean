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
import GoLean.NativeToIR
import GoLean.CLI
import GoLean.ChoiceTrace
