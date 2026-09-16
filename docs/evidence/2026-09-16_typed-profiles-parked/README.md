# Parking the typed-profile family — gate tails (2026-09-16)

[AGENT] lane `park-lane/typed-profiles-0916`; the consuming document is `docs/2026-09-16_typed-profiles-parked.md` §6. Every line below is the CAPTURED exit of the named command at the named commit; a killed or timed-out command decided nothing. Small by design (`scripts/check-evidence-size`); full logs stayed in the worktree's gitignored `.tmp/`.

- Toolchain: `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`); Lean per `lean-toolchain`; host linux/amd64, the shared box, other lanes idle by the box-wide build lock (`artifacts/build-lock.d`, owner file, released at exit).
- Bootstrap: `.lake` warmed by a plain `cp -a` of the primary checkout's build dir at IDENTICAL source `62fc8073` (the only read of the primary); `scripts/capped lake build` → `Build completed successfully (206 jobs)`, `EXIT=0`. `scripts/setup-deps` → `EXIT=1` (sandbox: `github.com:443 is not in the allowlist`; no network) — `deps/goose`, `deps/go` absent for every run below.

## Reproduction (from the repo root, at the commits named)
```
# bootstrap (worktree .claude/worktrees/park-typed-profiles, branch park-lane/typed-profiles-0916)
scripts/setup-deps > .tmp/setup-deps.log 2>&1; echo EXIT=$?                # EXIT=1 here: no network
cp -a /home/dev/projects/golean/.lake .lake && scripts/capped lake build > .tmp/warm.log 2>&1; echo EXIT=$?
# stage 2 (421ecc37)
scripts/capped lake build GoCoreAuditTests > .tmp/stage2-build.log 2>&1; echo EXIT=$?
scripts/check-core-audit > .tmp/stage2-gate.log 2>&1; echo EXIT=$?
# stage 3 (7ac513e6)
scripts/capped lake build > .tmp/build.log 2>&1; echo EXIT=$?
mkdir artifacts/build-lock.d && echo "$LANE $$ $(date -u +%FT%TZ)" > artifacts/build-lock.d/owner   # released by trap
scripts/ci --diff > .tmp/ci.log 2>&1; echo EXIT=$?                          # ci self-wraps in scripts/capped
# control: the same gate at the base, same sandbox (worktree detached at 62fc8073, then back)
git checkout --detach 62fc80731f0045c170634690bda1c26d1880f185 && scripts/ci --diff > .tmp/ci-base.log 2>&1; echo EXIT=$?
git checkout park-lane/typed-profiles-0916 && scripts/capped lake build > .tmp/rewarm-tip.log 2>&1; echo EXIT=$?
# witnesses in this directory
awk '/^DRIFT vs baselines\/native-full.tsv/{f=1;next} f&&/^[^ ]/&&!/->/{f=0} f' .tmp/ci.log > drift-rows-tip.txt
awk '/scripts\/ci summary/{f=1} f' .tmp/ci.log | grep -E '^\s+FAIL' | sed -E 's/^\s+FAIL //' > red-steps-tip.txt   # and ci-base.log -> red-steps-base.txt
comm -3 <(sort red-steps-base.txt) <(sort red-steps-tip.txt); comm -3 <(sort <base drift>) <(sort drift-rows-tip.txt) > tip-vs-base.txt
# records (on the staged stage-4 index)
scripts/check-bugs.sh; scripts/check-evidence-size; scripts/check-agents-alias; scripts/check-spec-anchors; python3 tools/ci_libraries.py check; git diff --cached --check
```

## Gate lines (the same table as the note's §6)
Environment first (it decides the shape of every line below): this sandbox has NO network (`curl https://github.com` → `403 … host github.com:443 is not in the allowlist`), so `scripts/setup-deps` EXIT=1 (goose/raft/go clones refused; fail closed) and `deps/go`, `deps/goose` are ABSENT. The native frontend refuses BY NAME without `deps/go/src` at the pin («native frontend unsupported: stdlib source root "deps/go/src" is not a Go checkout at the pin … run scripts/setup-deps --only go (fail closed)», reproduced by hand on `Corpus/coverage/exec/binary/little-endian`), and six gate steps need those checkouts. Per the standing rule (a sandbox block is asked about, not worked around) the lane did NOT clone from the primary's `deps/`; it ran a CONTROL instead: the same gate at the base commit in the same sandbox.

| Run (all `scripts/capped`, box-wide lock held) | Result |
|---|---|
| warm: `cp -a <primary>/.lake .lake` at identical source `62fc8073`; `lake build` | `Build completed successfully (206 jobs)`, EXIT=0 |
| stage 2 @ `421ecc37`: `lake build GoCoreAuditTests`; `scripts/check-core-audit` | EXIT=0; EXIT=0 — «100 GoLean modules in the closure (90 under GoLean.GoCore), all on disk; 51 required theorems present; 18712 declarations …; classical trio only», 5 compiled controls rejected by name, scratch removed |
| stage 3 @ `7ac513e6`: `lake build` (default targets, family gone) | `Build completed successfully (92 jobs)`, EXIT=0; every one of the 34 remaining `GoLean/GoCore/*.lean` is reachable from `Main` |
| **tip `7ac513e6`: `scripts/ci --diff`** | **EXIT=1, 714 s wall, clean tree.** 8 red steps: **the 5a pair** — `certificate provenance` («STALE certification: changed dependency build/files/GoLean.lean») and the certified row `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` — plus six ENVIRONMENTAL reds naming `deps/go`/`deps/goose`: `spec-anchor citations` (pinned spec checkout missing), `stdlib admission register`, `imported-goose verbatim` (`deps/goose` not a checkout), `frontend pins` ([twin-wire] emit refused; [hidden-dep-order] ok), `frontend unit tests` (`TestAtomicShadowModelTranscribesUpstream`: pinned upstream missing), `lowering-diagnostic tables` (`TestCalibrationAgainstWire`: the same refusal) and `baseline diff`: 331 rows = the certified row + 330 `-> now[FAIL/frontend-export]` (325 `PASS/-`, 4 `PASS/membership`, 1 `FAIL/lean-observation`) — no wire was produced for them. `differential coverage summary: cases=3676 pass=3098 fail=578` against the baseline's 3428/248. Green: escape-hatch scans, core build (warning-free), **core totality audit**, admission, declarations, wire boundary, method identity, unseq, eval (211), negative baseline, FloatVectors/inittask regeneration, executed library coverage (17 Tests modules, 7 steps). |
| **control, base `62fc8073`: `scripts/ci --diff`** (same sandbox, same lock) | EXIT=1, 972 s wall, clean tree. **7 red steps = the tip's six environmental reds + `baseline diff`**; `certificate provenance` GREEN («Certified build: compiled inputs match; sha256=0dec9436…»); drift block 330 rows, every one `-> now[FAIL/frontend-export]` (325/4/1 as at the tip); `differential coverage summary: cases=3676 pass=3099 fail=577`; all nine typed steps ok (the family still present) |
| **tip − base** | red steps: `comm` of the two summary blocks = **`certificate provenance` only**; drift rows: `comm` of the two blocks = **the one row `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` only** (the 330 `frontend-export` rows are byte-identical in both runs). That is exactly the 5a pair and nothing else: the change moved no corpus row. |
| records: `scripts/check-bugs.sh` / `scripts/check-evidence-size` / `scripts/check-agents-alias` / `scripts/check-spec-anchors` / `tools/ci_libraries.py check` / `git diff --check` | `check-bugs EXIT=0; check-evidence-size EXIT=0; check-agents-alias EXIT=0; check-spec-anchors EXIT=1; ci-libraries-check EXIT=0; git-diff-check EXIT=2 (a blank line at the end of the captured `drift-rows-tip.txt`; stripped, then EXIT=0)` — check-spec-anchors EXIT=1 is `deps/go` missing («pinned spec checkout missing (deps/go/doc/go_spec.html)»), the same environmental cause; the rest green |

Corpus rows CANNOT move here: the tracked delta outside the family is empty for `Corpus/`, `baselines/`, `tools/nativefrontend/`, `tools/coverageharness/`, `Main.lean` and every non-family `GoLean/**` file (`git diff --stat 62fc8073 7ac513e6` over those paths = the 56 Boolean*/Recovery* deletions only). The operator's commands to turn the six environmental reds into a judgment: `scripts/setup-deps` (network) or `scripts/setup-deps --from /home/dev/projects/golean` (a sibling's `deps/`), then `scripts/capped scripts/ci --diff`; the expected red is then exactly the 5a pair.

Files here: `red-steps-base.txt`, `red-steps-tip.txt` (the summary blocks' FAIL lines), `drift-rows-tip.txt` (the tip's whole drift block, 331 rows), `tip-vs-base.txt` (the two `comm -3` results: one step, one row).
