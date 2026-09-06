# Independent shared Iris customer review

[AGENT], 2026-09-06. **PASS for the frozen functional-customer increment**
against base `04109912`; this is not completion of O2 or the sprint.
The reviewer is the sprint integrator, independent of the customer author.
`source.sha256` and the 35 archived source files identify the reviewed input.

The review followed the call-layout/allocation, lifting, ghost ownership,
recovery and unwind rules through both functional proofs, actual admission
and setup, adequacy, singleton pool correspondence, choice transfer, and
driver result/output. It also inspected the gate, native artifact/control
checks and the exact exported-type ledger. No blocking defect remains in
this bounded increment.

The new call rule covers seven entry forms using one actual allocation
contract. Its parameter-world premise establishes layout validity; it does
not manufacture ownership of a captured pointee. Both handlers reuse the
one owned result cell. Fresh call slots have separate allocated resources.
The whole-program admission check includes the controls, and the functional
proofs compose local WP rules rather than presupposing the desired complete
execution. `customer_pure` discharges individual steps for every state with
the specified immutable context and every choice stream. Bounded successful
run projections supply termination only; Iris supplies the result property.

Independent replay in this separate worktree completed with exit 0:

- The complete customer gate freshly elaborated four semantic helpers,
  23 customer modules and the aggregate, checked 136 exports and 15,390
  local declarations, and rejected all 23 compiled audit poisons.
- Fresh native artifact checks and 3 A2 plus 5 shared/control differential
  cases passed, including input dependence, defer order and directness.
- Six additional kernel probes in `IndependentReview.lean` passed: framing
  an arbitrary third heap cell through both handlers and actual adequacy;
  preserving invalid UTF-8/NUL/LF panic bytes at direct recovery; blocking
  recovery at an ordinary-call barrier; deriving nil for an indirect
  handler; rejecting duplicate full ownership of one root; and retaining
  the input-dependent result and empty output for every choice list.
  The probe audit checked 15,399 declarations with the same allowed axioms.

`probes-1.log` preserves a failed initial invocation: its final audit command
used an incorrect namespace. The six substantive proofs compiled; correcting
only that command produced the passing `probes-2.log` and exit file.
Dependencies were copied from the pinned author's build into owned package
directories; the increment was freshly elaborated. This is not a clean-room
rebuild of every dependency. Author ordinary-CI evidence is archived as such;
its 3,607/394 corpus records are cached, not independently rerun here.

Remaining obligations are explicit: promote reusable contracts through the
facade, reconcile accepted dependency commits, independently review the
generic typed terminal classification, migrate through B7/I1, and run the
final integration gates. The existing Iris uncaught-panic-as-stuck policy
is unchanged. This review establishes neither universal Iris NotStuck for
typed programs nor a proved Go compiler correspondence or stable interface.
