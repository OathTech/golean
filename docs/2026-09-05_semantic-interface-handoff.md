# Semantic interface lane handoff

[AGENT], 2026-09-05. Base `700128f3`, branch `semantic-interface`.
The [USER] authorized the next-step sequence: land A2, integrate BUG-103,
promote the semantic interface, then the first A3 admission slice.

The semantic bridges are promoted under `GoLean.Semantics`, exposed by
`GoLean/Interface.lean`. Semantic choice/recovery/output regressions live in
`Tests/InterfaceContract.lean`; the ordinary core gate now runs their
post-import axiom audit and three compiled poisoned-module controls. Iris
remains outside that dependency graph. A1/A2 consume the promoted bridge
names and include the promoted modules in their own audits.

The design note specifies exact contracts and remaining internal dependencies.
No interpreter/frontend/corpus baseline change is made in this lane. The
original A1/A2 evidence remains a record of the original source snapshots.

Initial validation: all promoted modules and semantic regressions built;
ordinary capped CI passed, including 198 eval checks and the new core audit
(16 required exports, 193 constants, three named poison rejections). That
CI used the recorded 3593-case and 394-negative results from `75dcb6d`, not
a fresh corpus run. BUG-103's fresh combined-tree validation is owned by its
separate integration lane. Independent review now passes with no findings:
final A1/A2 gates pass (529/941 audited constants, three poison controls
each), A2 freshly matches native lowering and passes all three differential
cases. An extra unused private axiom in promoted `ProgramTrace` compiled
successfully and was rejected by all three audits. The report and logs are
preserved in this lane's evidence directory. Rebase onto landed BUG-103 and
combined-tree revalidation are next; that later state is not yet certified
by this initial review.

This is an experimental interface, not G-PIN or completion of Gate A.
The first A3 implementation proceeds in `gate-a3-admission`; B7/C1 and
general composition/adequacy remain separate obligations. Push has not been
authorized.
