-- This module serves as the root of the `GoLean` library.
-- Import modules here that should be built as part of the library.
import GoLean.StrictJson
import GoLean.GoCore
-- The surfaces kept on main for the raft-proofs customer when the relational layer was
-- retired (2026-10-20, tag relational/last-main-2026-10-20; docs/ARCHIVE.md): the
-- `stepFn_eqns` equation library with its attribute, the `Prefix`/`Finish` execution
-- statement with its proofs, the counted trace, and the kept part of `MachineSound.lean`
-- (`StepFnFacts`, reached through them). Enrolled here = default-build membership and the
-- core audit's two-way closure.
import GoLean.GoCore.Trace
import GoLean.GoCore.EquationsAttr
import GoLean.GoCore.Equations
import GoLean.GoCore.ExecutionStatement
import GoLean.GoCore.Prefix
-- The seeded-heap entry (executable): the seed and its pool wrapper.
import GoLean.GoCore.Seed
import GoLean.GoCore.SeedPool
import GoLean.NativeToIR
import GoLean.SeedFile
import GoLean.CLI
import GoLean.ChoiceTrace
