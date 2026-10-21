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
import GoLean.GoCore.PoolFacts
import GoLean.GoCore.ExecutionStatement
import GoLean.GoCore.Prefix
-- The initialiser's driver against the sequential driver and `Prefix` (raft-proofs G11, backlog
-- row 47, 2026-10-21): the premise-free dichotomy and the G-R4 family restated.
import GoLean.GoCore.InitDriverFacts
-- The relation-free single-goroutine bridge and projections, re-homed/restored 2026-10-21 (fix
-- round F1 of the retirement; pending the owner's ruling): `PoolFacts` (ex-MultiSound/PoolTrace/
-- ProgramTrace) and `PoolProjection` under its own name.
import GoLean.GoCore.PoolProjection
-- The seeded-heap entry (executable): the seed and its pool wrapper.
import GoLean.GoCore.Seed
import GoLean.GoCore.SeedPool
import GoLean.NativeToIR
import GoLean.SeedFile
import GoLean.CLI
import GoLean.ChoiceTrace
