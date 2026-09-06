# Recovery diagnostics follow-up (RS-1)

[AGENT] 2026-09-06. This is the source-bound follow-up to the independent
static review at parent commit `1ae77483`. That review freshly checked all
six original static modules, thirteen probes and 4,999 imported/local
declarations. Its sole required change, RS-1, was that valid Go outside the
string-payload profile and malformed unbound assignment both returned `body`.
The earlier `2026-09-06_recovery-static` evidence remains a historical snapshot;
its hashes describe the pre-diagnostic implementation, not these changed files.

`RecoveryDiagnostics.lean` now supplies total structural surface and placement
checks. `Statement.in_profile` and `Statement.placement` prove both checks
follow from the independently defined statement judgment. The definitions of
`FunctionTyped`, `ProgramTyped` and `RecoveryAdmission` are unchanged.
`checkFunction_iff` discards the two redundant checks in the soundness direction
and derives them from the judgment in the completeness direction. Admission
has therefore neither narrowed nor become a successful-evaluation predicate.

The diagnostic order first checks the supported statement surface, then the
machine's declaration placement, then binding/sort/call/capture/result typing.
This classifies profile membership, not arbitrary Go source validity. Kernel
controls distinguish valid `panic(true)` (`statementProfile`), an unbound
assignment (`body`), bare initialization (`declarationPlacement`), and a string
condition (`body`). A generic kernel theorem records unchanged admission.

The full focused command was:

```text
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/check-recovery-typing
```

It exited 0. `gate.log` records twelve fresh source elaborations, 46 required
exports, all imported local module origins, and five compiled forbidden-axiom
controls including a private declaration in the new diagnostics helper. The
fresh native emitter typechecked the existing Go `panic-bool-abort` fixture;
the complete emitted `outside.json` is retained, and its actual lowered entry
is rejected specifically as `statementProfile`. Whole original A2 and second
customer artifacts remain equal, with five differential PASS results and the
same input/defer-order/recovery-directness pins. `sources.sha256` binds every
new static module, test, gate/helper and native source used by this follow-up.

Ordinary CI exited 0 against this frozen source:

```text
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped scripts/ci
```

`ci.log` retains the full command output: all proof audits, 202 eval tests,
394 cached negative and 3,598 cached full baseline cases without regression;
two existing report-only findings, zero HIGH. Broad corpus records remain
explicitly cached at `10fefeb3`, as in the original static evidence. This
static lane changes no interpreter/frontend source; its five focused native
cases and the outside-profile native emission were fresh.

Independent follow-up review PASS is committed at parent `c2057e78`. The
reviewer freshly elaborated all seven core source bodies, thirteen updated
probes, and a separately compiled original `LegacyChecker`. The generic
`diagnostic_acceptance_unchanged` theorem proves the new and original checkers
agree on admission for every program, entry and argument vector. The audit
checked 5,078 local/imported declarations with only the classical trio; the
three admission-definition blocks were verified byte-identical. The reviewer
also inspected this full focused gate and fresh Go evidence. Final source
hashes match the reviewed snapshot.

No O2 runtime, progress, observation or Iris result is claimed here. Runtime
development uses the separate `typed-recovery-runtime` worktree.
