import GoLean.GoCore.FloatBits
import GoLean.GoCore.Machine
import GoLean.GoCore.StateWf
import GoLean.GoCore.StepFn
import GoLean.GoCore.Race
import GoLean.GoCore.Multi
import GoLean.GoCore.Consumes
import GoLean.GoCore.Locals
import GoLean.GoCore.EnumSpec
import GoLean.GoCore.EnumDedupCheck
import GoLean.GoCore.MachineEqb
import GoLean.GoCore.Admission
-- Typed-consumer sprint additive layer (landing chunk L1, 2026-09-07): the two
-- consumer-free helper modules are wired here so the default build elaborates them.
import GoLean.GoCore.Declaration
import GoLean.GoCore.PanicText
-- The executable core only. The relational layer (`MachineSound`, `UnseqSound`, `NPDRF`,
-- `MultiSound`, `MultiWfSound`, `MultiStreams`, `EnumDedupSound`) was retired from the build
-- 2026-10-20 (tag relational/last-main-2026-10-20); the proof-support modules kept for the
-- `stepFn_eqns` library and `Prefix`/`Finish` are enrolled by the root `GoLean.lean`.
