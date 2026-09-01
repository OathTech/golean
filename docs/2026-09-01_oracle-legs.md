# Oracle-matrix legs: the version sweep and the GOARCH=386 static leg

Lane: `t4-oracle-legs` (assessment lane — tracked output is this
report plus the two lane tools; NO baseline, gate, or corpus changes).
Mandate: fidelity decision 4, [USER]-approved
(`docs/assessment/decisions-2026-08-31.md` item 4; recommendation
`docs/assessment/synthesis.md` §4 item 4a/4b). Everything below is
[AGENT]-executed and [AGENT]-judged inside that mandate. Base commit
670d3351; oracle pin go1.26.5 (`baselines/go-oracle-pin`).

Both tools are LANE TOOLING, not gate steps: they never write
`artifacts/coverage` (the judged records) and never touch
`baselines/`.

---

## Leg 1 — the oracle version sweep: BUILT-AND-NULL-VALIDATED

**Tool:** `scripts/oracle-version-sweep`. Given
`GOLEAN_ORACLE_GO=<go binary | GOROOT dir>`, it re-runs the
differential corpus (`scripts/diff-coverage`, the standing runner —
nothing re-implemented) with the candidate toolchain first on PATH,
under `GOLEAN_ALLOW_GO_DRIFT=1` (the loud probe escape that mechanism
was built for), into a SEPARATE artifacts tree
(`artifacts/oracle-sweep/<candidate-version>/`; results/meta paths
forced inside it regardless of caller environment), then judges the
outcome against the recorded pin-run (`baselines/native-full.tsv`,
via `scripts/coverage-baseline-diff`). A drift row = a case where the
candidate's observable behavior no longer reproduces what the machine
was validated against — oracle movement surfaced per case, before any
re-pin conversation. `--sample N` draws a deterministic stride sample
from the full manifest for cheap probes.

Fail-closed properties: no candidate → refusal with the operator
command; unparseable candidate version → refusal; run meta not
recording the candidate version (shim didn't take) → refusal to
report the run as a sweep; infra exits (≥2) from the runner or the
differ propagate as refusals, never as green.

### Box inventory (checked, nothing installed)

One toolchain exists: `/usr/local/go` = go1.26.5 (the pin), the only
`go` on PATH. `~/go/bin` holds no toolchains (landrun only);
no `/usr/lib/go*`, `/opt/go*`, `~/sdk`. `deps/go` is the SOURCE
checkout of tag go1.26.5 (reference checkout, no built `bin/`) — same
version, useless as a second sweep point. Per the global-state rule,
no second toolchain was installed; providing one is the operator's
action (below).

### Null validation (2026-09-01, this worktree, commit 670d3351)

The sweep pointed at the SAME pinned toolchain must report zero
observation drift — the instrument-zero test.

    GOLEAN_ORACLE_GO=/usr/local/go/bin/go \
      scripts/capped scripts/oracle-version-sweep --sample 50

Result: **PASS — zero observation drift.** Exit 0. Scope: 50 of 2493
corpus cases (stride sample across the corpus; strict, confluent,
racy, and membership lanes all drawn). 48 PASS + 2 FAIL rows, and the
2 FAILs are exactly the baseline's recorded reds for those ids —
`coverage-baseline-diff`: "no regression: 50 case(s) run … match
baselines/native-full.tsv". Run meta recorded `go_toolchain go1.26.5`,
`go_drift_allowed 1`, `go_drift_actual false`; judged records tree
(`artifacts/coverage/`) untouched (verified absent after the run).
Summary artifact: `artifacts/oracle-sweep/go1.26.5/sweep-summary.txt`
(gitignored artifacts; reproduce with the command above).

Scope caveats, stated as bounds:
- Null-validated on a 50-case sample, not the full corpus; a full
  sweep costs one `ci --diff`-shaped run per candidate (~220 s at the
  last recorded full run) plus slow-tier policy: cached certified
  records verify by wire sha, so a FULL sweep of go-side behavior on
  slow rows means running the sweep with `GOLEAN_SLOW=1` semantics —
  quick sweeps cover the go-run oracle everywhere the quick gate does.
- Resolution is (result, stage) per case, the baseline record's own
  columns. A candidate that changes a recorded-FAIL case's failure
  DETAIL without moving its stage is below this instrument; PASS-row
  behavior changes (the signal that matters) always surface as flips.

**Status: BUILT-AND-NULL-VALIDATED, awaiting a second toolchain.**

### The operator command for a second toolchain (handed over, never run by an agent)

Either form is project-local; neither touches `/usr/local/go`, the
default PATH, or any global state. Example version go1.27.1 —
substitute the release under test:

    # (a) Go's own toolchain download, confined to this repo's artifacts:
    GOTOOLCHAIN=go1.27.1 GOMODCACHE="$PWD/artifacts/oracle-sweep/gomodcache" go version
    GOLEAN_ORACLE_GO="$PWD/artifacts/oracle-sweep/gomodcache/golang.org/toolchain@v0.0.1-go1.27.1.linux-amd64/bin/go" \
      scripts/capped scripts/oracle-version-sweep

    # (b) tarball, unpacked project-locally:
    curl -fsSL https://go.dev/dl/go1.27.1.linux-amd64.tar.gz | tar -xz -C "$PWD/artifacts/oracle-sweep"
    GOLEAN_ORACLE_GO="$PWD/artifacts/oracle-sweep/go/bin/go" \
      scripts/capped scripts/oracle-version-sweep

(Both need network; that too is the operator's call. The go1.26.6
float incident of 2026-08-21 — the event the pin file exists for — is
exactly the class a sweep at each upstream point release now catches
deliberately instead of by nightly surprise.)

---

## Leg 2 — the GOARCH=386 static leg: full-corpus census, 12 width-sensitive ids found

**Tool:** `scripts/oracle-386-static`. The p2 finding
(`docs/assessment/p2-keeps-a2a3bcd.md`, the C-8 break): the pinned gc
is its own 32-bit oracle at COMPILE TIME — `GOARCH=386 go build`
type-checks with 32-bit `int`/`uint` and rejects width-overflowing
programs amd64 accepts, with zero extra infrastructure. **Dynamic 386
is out of scope on this box**: 386 binaries abort in this sandbox
(exit 133 / SIGTRAP — p2's sandbox note, carried to the operator, not
worked around; decision 4 defers dynamic-386/gccgo/tinygo to a host
capability call). This leg is build-only, both arches, accept/reject
compared.

Method (per case, at the pin — the tool REFUSES on a drifted
toolchain, no escape, since its findings are claims about the pinned
gc's two width points):
- exec lane (2493 manifest rows): generate the SAME harness program
  the differential lane runs (`tools/coverageharness` — the trusted
  generation path; this tool invents no resolution), then
  `go build` it at `GOOS=linux GOARCH=amd64` and at `GOARCH=386`
  (GOPATH handed over for multi-package cases exactly as the runner
  does). amd64-reject of any kind is classified as an INFRA ALARM of
  this tool, never a finding — the dynamic lane builds every exec
  case at amd64 each `--diff` run.
- negative lane (390 rows): `go build` the case dir at both arches
  (the recorded lane's own invocation), additionally checking the
  recorded expected-rejection substring survives at 386
  (`REASON-DRIFT` otherwise).

### Full-corpus result (2026-09-01, commit 670d3351, ~4 min at 32 jobs)

| lane | cases | both-accept | 386-only reject | both-reject | reason drift | infra alarms |
|---|---|---|---|---|---|---|
| exec | 2493 | 2481 | **12** | 0 | — | 0 |
| negative | 390 | 0 | — | 390 | **0** | 0 |

Replay: `scripts/oracle-386-static` (artifacts under
`artifacts/oracle-386-static/{exec,negative}.tsv` + per-case build
logs; gitignored).

### The width-sensitivity table (all 12, = 2 case dirs)

Both dirs reject at 386 in the type checker, the exact R1 class
("which programs COMPILE — constant overflow at int boundaries"):

| ids | dir | 386 rejection | added |
|---|---|---|---|
| `strings/trimspace-repeat/{trim-ascii, trim-unicode, trim-all-space, trim-empty, trim-inner-runes, repeat-basic, repeat-describe-shape, repeat-negative, repeat-overflow, repeat-bound-refused}` (10) | `Corpus/coverage/exec/strings/trimspace-repeat/` | `cannot use 1 << 62 (untyped int constant …) as int value in argument to strings.Repeat (overflows)` (main.go:63, `repeatOverflow` — one function reddens the whole dir's package at 386) | 2026-08-21 (17eb6d5e, W4.3) |
| `sync/waitgroup-int32/{add-overflow-panics, add-wrap-noop}` (2) | `Corpus/coverage/exec/sync/waitgroup-int32/` | `cannot use 1 << 31 (untyped int constant 2147483648) as int value in argument to wg.Add (overflows)` (main.go:19) | 2026-08-10 (bd07413e — PRE-dates R1) |

These are not corpus bugs — both dirs deliberately probe 64-bit-int
behavior (Repeat length overflow at 2^63; the WaitGroup int32
high/low word split at 2^31). The point is evidence portability:
**these 12 differential cases exist only at the 64-bit point of R1's
{32,64} envelope** — at a 32-bit width the programs are not in the
language, so nothing they witness transfers.

### Cross-check vs R1's recorded scope (`docs/2026-08-11_latitude-inventory.md` §R1)

- R1 censuses the CLASS correctly ("also entangled: which programs
  COMPILE (constant overflow at int boundaries)…") but names ZERO
  corpus members, and one of the two hit dirs (`sync/waitgroup-int32`,
  2026-08-10) already existed when R1 was written. **Finding
  (record-level): R1's compile-acceptance entanglement now has 12
  live exec-corpus members, censused nowhere** — not in R1, not in
  the case dirs' cases.tsv (no width note in either), and not in the
  corpus feature tags:
- **Finding (corpus-census level): none of the 12 ids carries the
  `widths` feature tag.** The tag exists (Corpus/coverage/tags.tsv)
  and is in active use — 89 ids carry it — but the tagged set (the
  dynamic wrap/conversion probes: `ints/*`, dotprod/fib wrap rows,
  `constants/*-boundaries`, …) is DISJOINT from the
  compile-time-width-sensitive set found here: 89 tagged ids, 0 of
  them 386-reject; 12 386-reject ids, 0 of them tagged. The corpus's
  width census tracks runtime wrap behavior only; static width
  pinning of the evidence set was invisible until this leg.
- Negative lane, the entanglement R1 names explicitly ("the negative
  lane inherits the pin via go/types on the host"): **zero
  width-sensitive members** — all 390 recorded rejections reproduce
  at 386 with the recorded expected substring intact. The recorded
  negative baseline is width-STABLE across the {32,64} envelope as
  it stands; R1's entanglement is real but currently has no negative
  corpus member sitting on it. (Positive result worth having on the
  record.)

### Cross-check vs the grossmith arch386 findings (`docs/2026-08-20_grossmith-findings-2.md` §6, §3)

- §6 (dynamic gc-386 leg, generated programs): 870/4000 observation
  mismatches, ALL inside grossmith's declared `width_dependent`
  quotient, zero off-tag. Complementary, consistent picture: dynamic
  width divergence is the BROAD class (~25% yield on
  width-tagged generated programs — invisible to this static leg,
  which sees only compile-boundary constants), while static
  divergence is the RARE edge: 12/2493 (~0.5%) on our corpus, all in
  the declared R1 class, no off-census surprise. The static leg is
  the cheap standing instrument; §6's dynamic leg remains the deep
  one and stays host-gated.
- §3's discriminator direction ("offset too large" — amd64 rejects,
  386 compiles): zero corpus members (exec `AMD64-REJECT` count is 0,
  doubling as this tool's own infra control — the dynamic lane
  guarantees amd64 acceptance, and the census reproduced that 2493/2493).

Instrument limits, stated: build-only (no 386 execution — runtime
width divergence not covered); gc's accept/reject is the oracle, so
the FRONTEND's own width fold is a blind spot — p2 §1.1's leak
(unsafe.Sizeof folded into wire literals at HOST width by
`tools/nativefrontend`'s go/types) cannot be seen by any go-build
discriminator; R1's re-envelope obligation already names the frontend
Sizes config as surface, and the t1 fidelity round's unsafe handling
is where that class is policed.

---

## Recommendations ([AGENT] — wiring decisions are the user's)

1. **Version sweep: periodic, operator-triggered; not gate-wired.**
   There is no second toolchain on the box, so a gate leg would be a
   step that can never run (fail-closed would make it a standing
   red). Trigger it (a) at each upstream Go point release, (b) as the
   mandatory evidence-gatherer before any deliberate pin move (the
   charter already requires a full run + written reason for re-pins —
   the sweep IS that full run, produced without touching the judged
   records). Cost per candidate ≈ one full `--diff` (~4 min).
2. **386 static leg: periodic, cheap enough for nightly-adjacency.**
   Full census ≈ 4 min, go-only (no lake). Run it per corpus-growth
   arc (new case dirs are exactly where new width pinning slips in
   silently — both hit dirs arrived in ordinary landings) or as a
   nightly adjunct; per-commit gating buys little at 0.5% incidence
   and adds a 4-minute step (gates are speedbumps).
3. **Cheap follow-ups owed elsewhere (out of this lane's scope — no
   corpus/records changes here):** (a) tag the 12 ids (or the 2 dirs)
   width-pinned — either the existing `widths` tag or a dedicated
   `width64-only` marker so the two census meanings don't blur;
   (b) add the 12-member list to R1's entry as the live corpus
   members of its compile-acceptance entanglement, and note the
   negative lane's measured width-stability (390/390) there too;
   (c) any future 32-bit lane (decision 4's deferred dynamic legs)
   must exclude/replace these cases — the census output
   (`artifacts/oracle-386-static/exec.tsv`, replayable) is the
   exclusion list generator.
