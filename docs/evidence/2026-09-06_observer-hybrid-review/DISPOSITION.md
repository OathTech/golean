# Clarification: justified K3 repair, no new approval gate

The bounded design PASS in README is **not** a substantive objection to exposing
the sync-unwind row as a refusal. It reserves production validation and accurate
baseline reconciliation; it does not invent a user-approval requirement.

I reviewed the BUG-106 cause in the terminal-classification design and the hybrid
design's exact disposition against charter K3, §4, §6 and §7. The inherited
apparatus accepts a panic prefix while the execution can subsequently terminate
fatally; expected metadata cannot authenticate that terminal result. The later
system-frame draft also accepts forged payload/output. Retaining those guesses
would preserve a misleading PASS count. The new refusal instead records missing
evidence for a particular program-output boundary, without changing what fatal,
panic, deadlock or Go conformance mean.

For `sync/mutex-unlock-fatal/during-panic-unwind`, the justified intended movement
is **PASS → go-observation refusal** because fatal/panic prefix bytes precede
the runtime's private crash-channel activation. The native program still ends
fatally; GoCore's behavior and support are not narrowed by this apparatus repair.
O2 admission retains arbitrary strings and repeated panics. This is separate
from B7's required representation equivalence and I1's no-PASS-to-refusal rule
for moving IR markers. A reviewed, red-first repair and an explicit old/new
stage/cause ledger satisfy the applicable K3 process; no unresolved Go policy,
minimum-profile reduction or new trusted dependency has been established here.

I therefore endorse the exact named refusal **as the proposed fidelity-repair
disposition**, contingent on the implementation and fresh focused/full evidence
matching this argument. I do not endorse counting it as conformance, silently
re-pinning away its loss, claiming complete fatal observation, or changing a
charter gate. The production review must verify all retained accepted observations
and account for any additional losses; additional evidence could require a new
assessment. Broader runtime instrumentation remains a separate unestablished
alternative, not necessary merely to preserve the old unsound PASS count.

This clarification appends to the original sealed design review. The original
README, probes and source seal are unchanged.
