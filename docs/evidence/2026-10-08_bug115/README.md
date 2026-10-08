# Evidence — BUG-115 fixed: a map element as an `=` target outside the single-assignment fast path (lane `fix/bug115-map-multiassign-1008`, 2026-10-08)

[AGENT] fix worker, under [USER] Mike 2026-10-08 «While things are calm, can we fix some bugs?» (relayed by the [AGENT]
coordinator). Consuming records: `docs/BUGS.md` BUG-115 (the fix record), `docs/2026-08-19_triage-table.md` F6 / A3,
`docs/language-coverage-ledger.md` §2 `Assignment_statements` + §8 buckets + §8au, `docs/2026-08-11_latitude-inventory.md`
(the two Stage E5 F3 notes), `docs/changelog/20d3946d-WINDOW.md` (the draft row). Oracle go1.26.5 (`go version go1.26.5
linux/amd64`, the pin in `baselines/go-oracle-pin`); Lean toolchain the repo's `lean-toolchain`, `golean` built by
`scripts/capped lake build golean` at the lane tree; host linux/amd64 (the shared 125 G box, sibling lane gates running —
no timing claims here). Bulk scratch (`.tmp/`: the wire exports, the whole-corpus export comparison, the oracle harness)
was pruned at the lane's close; everything here regenerates from the commands below.

| File | What |
|---|---|
| `red-first-witness.txt` | the born package `Corpus/coverage/exec/maps/multi-target/` exported by MAIN's frontend (`6a90ba8d`) and by the lane's: on main 14 of the 19 subjects are refused by name («map element as assignment target outside a single assignment»), the 4 parenthesized spellings EXPORT an `index-addr` on the MAP VALUE (main's wire for `parenTupleTarget`'s assignment is printed); what the machine does with that wire (a `stuck`: «expected array or slice base for index address, got GoLean.GoValue.map …» — the quarantine's own hazard reached through the parentheses); and gc's per-subject oracle output (one process per subject), the source of every `expected_status` / `expected_reason` in `cases.tsv` |
| `diff-one-run1.tsv` | `scripts/diff-one` at the lane tree over 36 ids — the 19 born rows, BUG-115's six Cases rows, the noodler lane's three triage-F6 re-hits (`noodler/maps/{swap-with-missing,tuple-map-and-var,tuple-two-map-targets}`) and 8 in-package controls: 36/36 PASS |
| `ci-slow-run1.tail.txt` | gate run 1 (`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` at `7d61a5f6`, under the box lock, 1950 s): RESULT FAIL on exactly the expected pre-re-pin trio — the baseline DRIFT (19 new ids, all PASS; 9 FAIL/frontend-export → PASS/- flips, all on BUG-115's Cases line; no other row moved), the bug-index cross-check (BUG-115 marked fixed while its Cases rows were still FAIL / absent in the pre-pin baseline) and the certificate provenance pair (STALE on the frontend inputs `emit.go` + `lowerdiag/causes.tsv`; `imported-goose/channel/google-search` FAIL/membership at the run — «Fresh certification: unchanged set», a provenance refresh; the reconciler's 6 HIGH are the same pre-re-pin facts read from the records — check-bugs failing (C2), the 19 ids absent from the baseline (C3 ×2), §8's buckets already at 231 against the pre-pin baseline's 240 (C4 ×2), the stale certificate (C9); its 3 MEDIUM are the standing pre-existing ones, C13/C5, unchanged from train r74) — 3936 = 3704 / 232 at the run; every other step ok (core build warning-free, core totality audit, equations, pool spec, frontend pins — the raft twin wire byte-identical —, method identity, wire boundary, eval tests, the negative lane, the Go tests). The candidate (`artifacts/coverage/membership/imported-goose/channel/google-search/certification-candidate.json`: claim and observations identical to the tracked record, only the two input hashes and the receipt moved; receipt `git_dirty: true` — the then-untracked `README.md` of this directory, nothing else) was installed as `baselines/certified/imported-goose__channel__google-search.certified.json` (`tools/certification.py check-records` PASS); the baseline re-pinned from this run's rows with the certified row's PASS/membership kept (its run-1 FAIL is the stale record) |
| `ci-slow-run2.tail.txt` | gate run 2 at the re-pinned tip `d2406cac` (`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow`, under the box lock, 1317 s): THE GREEN RUN — RESULT PASS; 3936/3936 no regression (3705 / 231); re-pin guard ok (0 PASS→non-PASS; the 9 non-PASS→PASS flips report-only, covered by the baseline header's reason); certificate provenance ok; frontend pins ok (the raft twin wire = the pinned bytes); negative 394 no regression; core build warning-free, core totality audit, equations, pool spec (LANDED=M5, 48 discharged, 0 owed), method identity, wire boundary, eval tests, the Go tests all ok. Two honesty notes: (i) the run's dirty-tree marks (`git_dirty=true`) are ONE records-only edit made in the tree while the run was in progress — `docs/coverage-ledger.md`'s Maps row naming the born package — committed together with this tail; no runtime input, wire or baseline moved; (ii) the reconciler reported 2 HIGH at this run, both C4: the ledger §8 header still stated the pre-pin figures (3917 / 3677 / 240) — restated to 3936 / 3705 / 231 in the same commit; `tools/reconcile-records` at that commit: 0 HIGH, the 3 standing pre-existing MEDIUM (C13, C5 ×2), as at train r74 |

Conclusion (the one the records rely on): the `=` statement's map-element target lowers to the machine's existing map-element
PLAN (`{"target": "map"}` → `Assignee.mapElem`) in `emitAssignTargetPhase1`, so the legacy path realizes
spec#Assignment_statements' two phases through the assignment spine exactly as it does for every sibling target kind; no
core, decoder or wire-schema change; the wire of a program without the shape is byte-identical (the whole-corpus export
comparison: 1386 executable packages, 1353 identical, 25 export-failed on both — flag-dependent —, 8 differ = exactly the
packages holding the shape; the raft subject's twin wire byte-identical, `scripts/check-frontend-pins`).

Reproduction (repo root, the lane tree):

```
GO111MODULE=off go build -o .tmp/nativefrontend ./tools/nativefrontend          # the lane's frontend
(cd /home/dev/projects/golean && GO111MODULE=off go build -o <lane>/.tmp/nativefrontend-main ./tools/nativefrontend)   # main @ 6a90ba8d
GO111MODULE=off .tmp/nativefrontend-main --dir Corpus/coverage/exec/maps/multi-target --out .tmp/mt-wire-main.json
GO111MODULE=off .tmp/nativefrontend      --dir Corpus/coverage/exec/maps/multi-target --out .tmp/mt-wire-new.json
.lake/build/bin/golean native-json-run --input .tmp/mt-wire-main.json --function parenTupleTarget --fuel 100000
scripts/diff-one maps/multi-target/<id> ... evalorder/unseq-multi/map-target-nil-legacy-refusal ... (the 36 ids of diff-one-run1.tsv)
GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow
```

The whole-corpus export comparison: for every `cases.tsv` directory under `Corpus/coverage/exec`, run both binaries with
`--dir <pkg> --out <json>` and `cmp` the outputs (a package whose export fails on both — the differential's per-package
`--allow-hidden-dep-init-order` flag is not passed here — counts as neither identical nor differing).
