# Independent observer control-byte review

[AGENT], 2026-09-06 UTC. Reviewer: `typed-preflight`; implementation author:
`typed_contract_review`. **Bounded PASS: no blocking defect found in the
frozen core candidate.** This is an implementation/fidelity/negative-control
review, not completion of O2 or certification of the whole differential
corpus. The author's fresh full `scripts/ci --diff` was still running when
this report was sealed. Its outcome and any baseline reconciliation require
their own recorded disposition.

## Reviewed source and claim

The candidate was an uncommitted source-bound worktree over
`ff7173dd959435ede346c77318c29f13e16ed5f3`, at
`/home/dev/projects/golean/.claude/worktrees/typed-observer-controls`.
`provenance.json` records every reviewed executable/fixture source hash;
those hashes were checked again before sealing with no drift. The archive
contains exact candidate sources and snapshots of the author's design,
BUG-105 entry and focused evidence. It excludes the separately evolving
diagnostic increment in `membership-sampling`, `gotest-triage`,
`cedar-census`, and `check-observer-tools.py`.

The supported claim is repair of valid-UTF-8 control-byte transport in
`diff-coverage` strict and membership/confluent paths, preserving the
existing first-line and stderr-splitting policy. Native Go bytes remain in
separate raw descriptor files until validated/encoded. The actual message,
including NUL/SOH/CR, supplies the observation; the manifest reason is only
a gate. No GoLean semantic implementation or oracle/toolchain pin changes
are part of this candidate.

## Evidence and adversarial checks

The reviewer copied the frozen Go harness into a private scratch directory,
built it independently, and ran its complete unit suite successfully
(`unit.log`, exit 0). The independent `review.py` then recorded **324
successful checks** (`results.json`, `review.log`, exit 0):

| Checks | Count | Result |
| --- | ---: | --- |
| Every ASCII byte in first panic line and program-output prefix | 256 | LF alone ends the message; CR, NUL, SOH, TAB and DEL survive where observed |
| Unicode/quoting and fatal-unwind continuation payloads | 4 | Decoded bytes match independently specified payloads |
| Four malformed UTF-8 encodings in message, output and raw JSON | 12 | Named refusal, exit 3 |
| Raw JSON control bytes 0–31 | 32 | Invalid JSON refused before shell transport |
| Large integer text and escaped controls in valid stdout JSON | 1 | Original text preserved exactly; no numeric reencoding |
| Diagnostic rendering of all 256 byte values | 1 | ASCII representation preserves escaped invalid/control bytes |
| Actual extracted sampling functions with fake external oracle | 6 | Raw descriptors preserved; status membership and stdout-only false report rejected; plain/`-race` forwarding correct; reused sample files do not leak prior bytes |
| Four real pinned-Go runs plus independent message/prefix checks | 12 | Plain panic, recover/repanic, fatal during unwinding and invalid-UTF-8 panic agree with the helper's declared behavior |

The synthetic checks are apparatus evidence, not Go conformance. The real
Go probes use `go1.26.5 linux/amd64` and independently emit NUL/SOH/CR/LF;
their raw stdout/stderr and generated Go source are retained. Their purpose
is to challenge report-shape assumptions, not to compare Lean execution.
Sampling probes use the reviewer's existing GoLean binary only for the
unchanged observation comparator; its hash is recorded, and this is not a
fresh model build or a new runtime-validation claim.

Source review additionally checked both callers of `go_run_oracle`, strict
classification, reason matching, fatal exit-status checking, the sampling
loop, fd separation, and CI wiring. Classification reads the raw stderr
file, never the diagnostic string. Successful stdout is validated before
Bash can drop NUL. The encoded message/output strings are valid JSON before
shell transport. `observationText` preserves JSON text; schema validation
still belongs to the existing Lean comparator. Sampling's alternation,
minimum draws, saturation and per-sample checks were not weakened.

The author's gate was inspected, including its extraction of the real
strict/sampling shell code and its four mutation controls. Each mutant is
required to compile before a targeted behavioral test must fail: NUL
deletion, raw SOH JSON, whitespace/CR trimming, and NUL removal before
stdout validation. The author's saved gate log reports all 26 apparatus
probes and all four controls passed. This log is attributed author evidence;
the reviewer did not rerun that full gate merely to duplicate it.

The author's red eight-row and green nine-row native records support the
specific repair. Five initial failures comprise one decided NUL mismatch
and four invalid-oracle-JSON failures; these are distinguished in the
ledger. The additional child-confluent row has only green evidence. The
initial raw stderr files were overwritten during the author's green rerun;
red log/TSV/meta survive, and `green-native-raw-streams.json` is correctly
labeled green-only. No red raw-stream reconstruction is claimed.

## Boundaries and remaining obligations

- Invalid UTF-8 in an **observed** message/output/raw-JSON field is refused;
  there is no representation decision for invalid Go-string bytes. Only
  the selected first panic line is observed; this is not validation of the
  unobserved remainder of a runtime report.
- Existing ambiguity, trace-header, trailer and first-line splitting rules
  remain the policy. This review does not prove a generic parser theorem
  for adversarially fabricated runtime-looking output. Existing race-report
  limitations in `splitStderr` are unchanged.
- The selected output channel remains program stderr, with abort stdout
  retained separately for diagnostics. This is not a new claim that every
  possible Go stdout effect is modeled.
- BUG-004/R-1, rendering quotients, dynamic boxing identity, generic UTF-8
  decoder correctness, and O2 terminal contracts are not discharged here.
- The separate three diagnostic scripts still require their own repair and
  review. Neither this verdict nor BUG-105 should be read as a claim that
  every repository oracle path was already fixed.

The inspected design/BUG-105 wording accurately distinguishes the repair,
red-result kinds, observed-line UTF-8 scope and pending full gate. No change
of observer policy or baseline is authorized by this review.

## Reproduction and seal

`commands.txt` records the exact fresh build/test/probe commands and resource
environment. `review.py` is the executable probe specification;
`results.json` records each subprocess argv, exit and raw output hashes.
`probes.tar.gz` retains all scratch sources, inputs and raw outputs, plus
the exact candidate and attributed author snapshots; rebuildable binaries
are excluded and hashed in provenance. `archive-members.sha256` inventories
every archive member, and `archive-verification.json` records a complete
post-write verification. `SHA256SUMS` seals every top-level report artifact
except itself. The archived scratch path and provenance describe the
historical run; a replay should use a new private scratch directory and
rebuild the copied harness there rather than mutate this evidence.

No parent/author worktree source, runtime source, dependency pin or baseline
was edited by the reviewer. No main merge or push was performed.
