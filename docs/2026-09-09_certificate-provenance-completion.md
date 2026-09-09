# F8 certificate provenance — review handoff

[AGENT] 2026-09-09. **DONE ON BRANCH; independent adversarial review pending
the user.** Implementation `7d60c8bf12ef5d34d1ef9901c213cd724926d78f` on
`fix/certificate-provenance`, based on main `8cc3d5c8`. No merge or push.
This closes the implementation of master-plan-v2 P1 / project-gate-audit F8;
landing remains subject to review and explicit sign-off.

[Charter](2026-09-09_certificate-provenance-charter.md) ·
[Design and refresh protocol](2026-09-09_certificate-provenance-design.md) ·
[Measured evidence](evidence/2026-09-09_certificate-provenance/result.json).

## Delivered contract

Both slow cache consumers now require the complete enumeration claim and
current semantic/build inputs to match a successful certification record.
The executable carries its compiled build manifest; an old executable beside
new sources is refused. `scripts/build-certified` forces the stamp to rebuild
when its external inputs change, uses Lake's content-rehashed build, and checks
the resulting executable against those inputs.

One inventory/validator serves cache reuse, fresh enumeration, CI, C9 and the
broader release rule. It covers 105 build files, 186 apparatus files, the
pinned compiler's 12,271 distribution files, the oracle pin/version and the
effective invocation. New ignored sources are included; missing dependencies,
excluded import roots, external Lake packages, alternate build configuration
and extra native-link/target options fail closed. Documentation and equivalent
checkout locations retain reuse.

Fresh enumeration owns the actual subprocess and exit, preserves refusal
diagnostics, removes an old candidate before starting, and publishes a new
candidate only after checker acceptance, exact set equality and stable
input/build/wire checks. Ordinary CI never updates tracked records. A changed
set remains a finding. Version 1 covers checked dedup certification, including
both membership and confluent consumers; it covers the entire current slow
tier. Other certification modes require an explicit extension.

The trust assumption is the checked-in certifier, compiler/Lake and local
host, as detailed in the design. This is content-bound build provenance, not
a cryptographic signature or protection against a hostile host forging output.

## Validation and unchanged scope

| Check | Result |
|---|---|
| Final implementation `scripts/ci --slow`, before commit | PASS, captured exit 0, 1,179.888 s; accurately marked dirty |
| Full clean-source `scripts/ci --slow` at `7d60c8bf` | PASS, captured exit 0, 1,204.046 s; `git_dirty=false` |
| Native baseline | All 3,665 rows match: 3,417 PASS / 248 tracked FAIL |
| Negative baseline | All 394 rows match and PASS |
| Evaluator tests | 207 PASS / 0 FAIL |
| Slow checked enumeration | Same six members, wire and params; `checkCert` accepted; 157.464 s under the full worker load |
| New provenance controls | 68 PASS, including a compiled Ops diagnostic mutation at unchanged wire and both actual shell consumers |
| Complete confluent cache runner | Real frontend, Go oracle and coupling positive; stale-input negative rejected by name |
| Ordinary membership cache runner | PASS, explicitly `CERTIFIED-CACHED`; 32 Go draws, five members exhibited, one unexhibited; coupling checked |
| C9 / reconciler HIGH findings | Zero / zero |

The native and negative baseline files are byte-identical to main. The
certified TSV's observation data, wire hash and literal parameters are
unchanged; only its human-readable certification header was refreshed, and
the adjacent JSON provenance record was added. Every file under `GoLean/`
and `Tests/` is unchanged. Runtime plumbing is confined to `Main.lean`.
The Lean and Go pins, frontend wire and theorem statements are unchanged.

The clean certificate's captured source is `7d60c8bf`, with `git_dirty=false`.
The final records-only commit does not change its input identity. The ordinary
cached probe also ran at that clean code commit, reusing the matching initial
provenance; the subsequent refresh records the clean full run's receipt.

The remaining reconciler findings are the pre-existing C5 frontier citation
and C13 historical Go-version mentions (both MEDIUM). They do not concern F8.
No subagents were commissioned; these checks do not constitute the user's
independent adversarial review.

## Measured cost for acceptance

All measurements used a warm build with symlinked dependency artifacts,
32 GiB memory cap and three Lean threads. Full corpus runs used 12 workers;
the focused cached run used one. These are observed wall times, not a paired
benchmark against an older implementation.

| Measurement | Wall time |
|---|---:|
| New always-on provenance CI step, including controls and current-record check | **73 s** |
| Controls within that step | 61.320 s |
| Standalone current-record check | 10.993 s |
| Certified incremental build, total | 5.153 s |
| Shared cache validation/read, total | **5.035 s** |
| Entire focused cached case, including Go samples and coupling | 31.386 s |
| Complete clean `ci --slow` | **1,204.046 s** |

The new CI step is about 6.1% of the observed clean full-gate time. This does
not claim the entire gate slowed by exactly that amount. Conservative
script/tool hashing deliberately makes apparatus edits require recertification.

## Evidence and remaining handoff

The tracked evidence is a compact JSON result with source refs, invariant
hashes, captured exits, timing receipts and log digests. Raw logs remain
ignored under this worktree's `artifacts/f8/`; the clean full log is
`artifacts/f8/ci-clean.log`. Successful control scratch was deleted, with
dependency oleans symlinked rather than copied. Failed development fixtures
retain their reason files. An intentionally interrupted partial gate and an
earlier passing gate before the diagnostic correction are explicitly recorded
in the charter; neither is substituted for the final-source runs above.

Next: the user's independent adversarial review, then any required fixes and
explicit merge sign-off. The merge train must snapshot main before merging,
run `release-check --base <snapshot>`, and satisfy the broadened 5a rule.
The pre-F8 main tip lacks v1 metadata, so this landing requires the train's
fresh merged-tip slow certification even though the branch has its own.

[AGENT] Final record checks passed after installing the clean receipt. `release-check --base 7d60c8bf` exits 0 for the records-only update; `--base 8cc3d5c8` exits 1 and explicitly requires the train’s recertification. Evidence-size and AGENTS-alias gates pass unchanged.
