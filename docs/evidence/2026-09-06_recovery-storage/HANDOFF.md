# Recovery runtime lane handoff

[AGENT] 2026-09-06. Worktree `typed-recovery-runtime`, base `212842a9`.
Six supporting modules, twelve kernel regressions, full imported-local audit
and eight compiled poison controls are complete. Dedicated gate and ordinary
CI exited 0; independent review PASS is parent `efc2712c`. Exact provenance
and limitations are in the sibling README, logs and hash inventories.

The parent owns `RecoveryResultRoots`, generic setup/initialization and
initial `MachineWf` in `typed-recovery-setup`; this agent owns the complete
control invariant and preservation/progress. The parent developed against
exact copies of the frozen Store/Environment/Allocation helpers and must
integrate their committed sources and rebuild before accepting its increment.

Control development is currently an explicitly temporary, ignored source
tree at `/home/dev/projects/golean/.tmp/recovery-control.2AfOcr`. Delivery,
ControlData, Control, ControlMono and RecoveryWalk freshly compile there;
ControlData imports an exact temporary copy of the parent's ResultRoots.
The structural definitions distinguish boxed panic arguments, target
addresses and closure values, preserve actual scope/signature/result/defer
facts, enforce joint sequence effects, and exclude return-to-stop. The actual
recover walk has a typed rebuilt-continuation proof. These drafts have no
final audit, full all-successor proof or driver contract yet and are not
included in this supporting increment's acceptance.

Next: commit/integrate these reviewed helpers under standing feature approval;
continue call/defer/panic/recover preservation and generic setup composition;
promote the control proofs with source-bound audits and reviews, then prove
actual driver/readout and reusable Iris customer contracts. Observer handling
of arbitrary invalid UTF-8 and equal recovered payloads remains an independent
mandatory repair. Do not narrow the admitted profile to sidestep it.

Main merge and push remain user-approved actions. No live processes remain
from this increment's passing gate or ordinary CI.
