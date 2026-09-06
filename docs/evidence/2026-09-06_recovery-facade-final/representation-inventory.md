# Recovery facade and customer migration inventory

[AGENT] Originally prepared 2026-09-06 against terminal source fingerprint
`3ecd4123092b3599f3faa6ff39c4283ea23012c01e355f04e8d107ead7a4f693` and
the frozen shared-customer source manifest. The implementation described below
is now present in the reconciled candidate. Final author gates passed;
independent integration acceptance remains pending. The facade remains experimental.

The terminal worktree has fast-forwarded to the root's sealed observer
integration `414a2abe`; all 14 terminal draft inputs remain identical.
Snapshot ref `snapshots/typed-terminal-pre-observer-20260906`, the tracked
patch and untracked archive under `artifacts/terminal/` preserve the prior
state. The accepted shared checkpoint `bd31dd5d` was subsequently integrated
at `658fe3eb`, and accepted renderer `819182b5` at `ccf826cb`. Their exact
semantic bytes are unchanged in the candidate. The original source packets
and pre-renderer stash `d8d6c19c` remain preserved.

## Semantic promotion

The implementation exposes `RecoveryCallLayout`, `RecoveryChoices` and
`RecoveryPoolObservationTyped` to the experimental `GoLean/Interface.lean`
surface (transitive imports may make explicit duplication unnecessary).
The first supplies exact setup and all seven frame-entry layouts; the second
supplies the unchanged-choice success transfer and singleton output theorem;
the last supplies actual program terminal classification and metadata.
The facade now states the actual
every-fuel/all-choice contract and its default-platform, unbounded-model-heap,
empty-output, no-generic-termination and no-Iris-resource boundaries.

Generic observer erasure/provenance is exposed through the renderer owner's
accepted facade delta. The interface's named export inventory, module
inventory, fresh elaboration loop and compiled-poison tests include the new
semantic helpers and terminal tests. Ordinary CI includes the dedicated
terminal gate and preserves every existing gate and poison. The terminal gate remains
useful as the focused iteration command.

## Customer imports and representation boundary

| Customer source | Current direct semantic dependency | Final action |
|---|---|---|
| `Admission.lean` | `RecoveryInvariant` | Import the facade and retain the existing admission proofs. |
| `Call.lean` | `RecoveryCallLayout` | Consume the exposed layout contract; keep seven-form `CallSite` and the Iris allocation/WP proof in the customer. |
| `Unwind.lean` | `RecoveryWalk` | Consume its exposed transitive contract; keep local continuation shapes explicit. |
| `Readout.lean` | `RecoveryChoices`, `MultiSound` | Use the facade's same-fuel pool, choice and actual-readout contracts. Preserve independent fixture termination witnesses. |
| `Program.lean` | `Multi` | Import the facade for the experimental exposed GoCore syntax; the whole native artifact and its tested pin remain unchanged. |
| `SharedProgram.lean` | Already imports facade plus the native fixture test artifact | Preserve complete-artifact admission and all controls. |

An import change does not create an abstract representation barrier. The
adapter still depends on machine `Config`, continuation and state constructors
in `Heap`, `Ghost`, `Lifting`, `Rules`, `Call`, `Return` and `Unwind`. Those
modules isolate state interpretation, lifting, concrete transition shapes,
ownership allocation and recovery context; `Program`/`SharedProgram` and
example configuration definitions necessarily name their admitted syntax.
The facade remains experimental and B7 must migrate these dependencies.
Do not claim an interface stable enough for C1 or a whole-machine-free
customer merely because direct core imports have been replaced.

Both customers already use the common setup, seven-form call/allocation,
writeback/unwind and adequate typed-program readout rules. Preserve those
statements and proofs. Add terminal contract applications from the facade:
unconditional no-refusal/classification for admitted A2 entries and arbitrary
shared input, and an actual uncaught-program record via the proved panic/record
equivalence. Normal/recovered program conclusions remain Iris-derived and
NotStuck remains conditional on their customer proof, never a corollary of
admission for uncaught panic.

## Final evidence

After owner acceptance, preserve the original 35-source shared packet and
14-source terminal packet as historical author evidence. Record exact
dependency-commit reconciliation, then create a new final union fingerprint.
Refresh exact theorem types, interface/customer dependency inventories,
compiled-poison audits, native artifact comparisons and the eight A2/shared
differential rows. Run the default build and ordinary CI at the integrated
source. Final source-bound independent review and B7/I1 migration remain
required under the approved sprint charter; the integrator owns acceptance.
