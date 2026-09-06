# Frozen R-1 implementation: independent review request

[AGENT] typed-string-members, 2026-09-06. The candidate is uncommitted work
on `typed-string-members` at dependency merge `620489c9`. Its exact source
inventory is `docs/evidence/2026-09-06_string-panic-members/production-candidate-source-v2.json`;
the checked source is held fixed during review. The implementation and
certificate design documents state the proposed contract. This request is
not an acceptance finding or completion claim. The original 178-input
inventory is preserved as `production-candidate-source.json`; it omitted
the executable `Main.lean` and `GoLean.lean` entrypoints and did not establish
complete apparatus binding. The corrected 180-input candidate adds both,
independent missing/changed-byte tests, and two compiling omission mutants.
The original unfinished CI run was terminated before source changed and
before any full-corpus run; its log and termination record remain evidence.

Review the constructive `PanicText` LF-byte-prefix and all-byte escape proofs,
the guarded direct-decoder renderer in `Machine`, and `StringPanic`'s generic
boxed-string head/positive-fuel abort equations. The direct-or-escape theorem
does not assume the decoder's correctness. Only the escape grammar is proved
injective; a test explicitly demonstrates collision of complete rendered
text. Non-string equal-payload refusal is retained. Check the actual driver
CLI against the reviewed generic observer, which retains a complete reached
string chain and proves all-input erasure to the shipped pool/program/Ints
driver. The CLI accepts no caller payload certificate.

Review the fixed thirteen-role apparatus: eight exact controls, five actual
abort membership controls, complete subject/control source inventories and
fresh wire bindings, exact copied subject sources in the distinct broader
control artifact, raw Go report transport, terminal/exit/output checks and
compiled mutation controls. The selected machine message is checked against
the fixed byte-preserving member construction from the actual full string
chain; it is not equated to gc's report or used to infer payload type.
The typed subjects additionally pass the independent O2 checker on their
identical lowered artifact. The historical `repanic-same-value-abort` row
explicitly uses broader concrete source/control evidence and does not claim
O2 admission. The two fixture-argument documents relate every kind/byte/order
companion to its corresponding abort body.

The generic O2 theorem connecting admission/runtime invariants to all terminal
outcomes is still owned by the recovery terminal lane. This R-1 candidate
supplies the actual observer, renderability theorem and independently checked
admission needed by that integration. The corpus results recorded here are
bounded concrete execution evidence pending production review and the final
typed theorem integration; they do not discharge O2 on their own.

The evidence directory retains the original red renderer experiment, initial
eight-case corpus records, all raw-native and zero-fuel controls, nine valid
Go semantic mutations, four otherwise-valid capture/exit refusals, four
compiled Go-helper and five compiled Python-checker mutations, and the
pre-integration 21-poison interface gate. The post-observer build passed;
refreshed focused and interface gates are recorded there as they finish.
`post-observer-unions.patch` shows the six build/interface/CI unions. All
other 71 working files were byte-identical across dependency integration.
Draft fingerprint updates preserve earlier pins in an archive and change
no subject/control/wire/observation expectation. Full CI --diff is still a
required gate, and neither a main merge nor a push is authorized.
