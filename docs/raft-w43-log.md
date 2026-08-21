# Raft W4.3 campaign log — the corpus train (W4.3 + W4.4 + owed rows + membership greens)

Lane: `raft-w43` (worktree `.claude/worktrees/raft-w43`), branch `raft-w43`
off `main` @ `521f5b57` (the W4.2 tip). Charter (the ratified launch plan,
lane A): the rendered-tier surface (the 9 named refusal causes,
guardrails-first per cause), conf-change support in the replay env, the
FULL trace differential as the milestone, the W4.2 owed-rows wave, and the
w32 charter §S3(b) membership-green conversions (case-level). Sole owner
of `tools/nativefrontend`, `Corpus/`, `baselines/`, `raftsubject/`,
`tools/raftsubject/`, `raftharness/`.

Read-first companions: `docs/raft-w42-log.md` (item 4 — THE TIER-STRENGTH
BOUND, the refusal-cause census, the owed-rows table, H-20),
`docs/2026-08-20_machine-twin-harness-design.md` §7,
`docs/2026-08-20_w32-re-envelope-charter.md` §Rulings R-1 + slice 3(b),
`docs/raft-w41-log.md` (the fmt desugar mechanism, E5/E5-T precedents).

**THE TIER-STRENGTH BOUND, carried at the head as the charter directs:**
the ok-tier is blind to delivery-order unfaithfulness (it asserts
acceptance only) and the machine/byte tier is oracle-symmetric (the same
mirror on both sides — a mirror bug is invariant under it). The rendered
tier is the FIRST tier that can falsify the replay mirror: rendered
expectations carry message order, drop markers and per-node Ready contents
verbatim against upstream's own recorded output — the only oracle in this
instrument family external to us. Every milestone claim in this log states
that bound.

## Environment notes (2026-08-21)

- Fresh worktree; `scripts/setup-deps --from /home/dev/projects/golean`
  exit 0 (goose 3be88bb, perennial 43d4efa, raft 56e3200, iris-lean
  3877dbe, go c19862e5f8) AND the Lake packages (iris 3877dbe, batteries
  fa08db58, Qq f463249) — the script populates `proofs/.lake/packages`
  now, per its updated pins table; output checked as the charter asked.
- This lane touches runtime code (`tools/nativefrontend`) and `Corpus/`,
  so per-landing gates are `GOLEAN_MEM_MAX=24G scripts/ci --diff` (no
  hatch). Three lighter lanes run concurrently: `free -g` checked before
  every full gate (84G free at the initial run), gates staggered.
- The initial full gate (`ci --diff`, this worktree's first recorded run)
  was started before any change: `artifacts/w43/ci-initial.txt`.

## The item-1 surface, measured before any code (2026-08-21)

The 9 named refusal causes (w42 census, `docs/evidence/2026-08-21_w42-census/`)
plus the riders a source read of every renderer found — the full set the
rendered tier needs, each with its gc probe recorded
(`artifacts/w43/probe-fmt/`, run at go 1.26 toolchain in this tree):

| # | cause | sites | mechanism |
|---|---|---|---|
| 1 | `fmt.Fprint` (unformatted) | DescribeReady, majority.Describe, progress/tracker String — every subject site is a SINGLE argument of static string type | desugar: Fprint(w, s) → w.WriteString(s); multi-arg/non-string refuses |
| 2 | `fmt.Fprintf`/`Fprint` over `*bytes.Buffer` | describeMessageWithIndent, DescribeEntries | E5-T shadow model of bytes.Buffer (the Builder precedent); writer allowlist gains *bytes.Buffer |
| 3 | `%v` over `[]uint64` | DescribeConfState (4 verbs) | compile-time COMPOSITE rendering: %v/%+v over slices/structs of modeled element kinds, recursively, specialized per static type; gc-probed: `[1 2 3]`, nil and empty both `[]` |
| 4 | `%q` over `string` | StateType.MarshalJSON | matrix cell add (quoter exists; ASCII bound unchanged) |
| 5 | `%+v` over struct | logSlice.valid (entryID) | the composite mechanism of #3; `{term:3 index:9}` gc-probed; bounded to struct shapes whose fields are in the matrix, fail closed beyond |
| 6 | `strconv.FormatUint/FormatInt` | quorum Index.String, VoteResult.String | E5 shims, general base 2..36 (gc-probed incl. base 36 + illegal-base panic) |
| 7 | `strings.Split` | ConfChangesFromString | E5 shim, byte-scan (upstream's own semantics is byte Index); EMPTY separator fails closed (rune splitting — recorded bound) |
| 8 | `slices.SortFunc` | MajorityConfig.Describe (H-5/W1.2) | injected GENERIC E5 shim (insertion sort) through the ordinary stencil pipeline — no GoCore change (GoCore is not this lane's); tie order is recorded latitude (upstream: "not guaranteed to be stable"), guardrail rows tie-free + one tie-insensitive-observation row |
| 9 | `Sprintf`-spread (+ `Sprint`-spread, non-const formats) | DefaultLogger bodies; the RECORDING logger | runtime-formatter E5 shims (`SprintfDyn`/`SprintDyn`): runtime format parse over the modeled verb set, runtime kind dispatch, fail-closed panic outside; Sprint's space rule gc-probed ("space iff neither neighbor is a string") |

Riders (found by reading every renderer the 309 blocks reach; each is a
named refusal today):

- **`%t` over bool** (DescribeReady's `MustSync=%t`) — parser+matrix add.
- **width `%5d`** (MajorityConfig.Describe, the one width in the tree) —
  parser accepts digit width for `%d` only; space-pad left, sign inside
  (gc-probed `[    7]`, `[  -42]`).
- **`strings.Repeat`** (MajorityConfig.Describe) — E5 shim (negative
  count panics with upstream's message).
- **plainpb enum `String()` bodies** (MessageType/EntryType/
  ConfChangeTransition/ConfChangeType) — today fail-closed panic stubs;
  traces render `MsgApp`/`EntryNormal` etc. `derive.py` gains real
  bodies over the `_name` maps (upstream generated code is
  `proto.EnumName` over the same maps; unknown values fall back to the
  decimal string, mirroring EnumName). This REMOVES a recorded delta
  (the stubs) rather than adding one. Message-typed `String()` stubs
  (proto text format) stay panic stubs — no trace needs them
  (Describe* exists precisely to avoid proto-text detrand instability).
- **`%v` over `[]ReadState`** (DescribeReady's ReadStates line — dead in
  every supported trace but inside a function that must lower) — covered
  by the composite mechanism of #3 (struct of uint64 + []byte; `[]byte`
  fields render as decimal byte lists, gc-probed).

## Plan of record (commit-sized slices, guardrails first per slice)

1. fmt matrix smalls: %q-over-string, %t, %d width. (frontend + rows)
2. %v/%+v composites (slices, structs, recursion, Stringer elements
   consulted inside composites — gc-probed D1–D4). (frontend + rows)
3. Fprint + bytes.Buffer model + writer widening. (frontend + rows)
4. strconv.Format* + strings.Split + strings.Repeat shims. (frontend + rows)
5. slices.SortFunc generic shim. (frontend + rows)
6. dyn Sprintf/Sprint (spread + non-const formats). (frontend + rows)
7. derive.py enum String bodies + subject re-derive + census re-run.
8. Item 2: conf-change support in replayenv + tracereplay
   (propose-conf-change bodies, ApplyConfChange in the apply path).
9. Item 3: the rendered tier — the recording logger (replay-env-only),
   the handler-output mirror (withIndent, log-level, "> N handling
   Ready" wrappers, deliver-msgs describe lines + drop markers +
   ordered recipient list — retiring latent divergence #2), the full
   28-trace differential, per-family agreement report.
10. Item 4: the owed-rows wave (w42 table cross-checked; land the rest).
11. Item 5: the §S3(b) membership-green conversions (C3/C4, case-level).

Judgment calls are logged inline per item as JC-30+ (continuing W4.2's
numbering); checkpoints every ≤5 units.

## The initial gate (pre-change record)

`GOLEAN_MEM_MAX=24G scripts/ci --diff` at `521f5b57`, unchanged tree:
**RESULT: PASS**, `baseline diff FULL (2343/2343, no regression)` —
`artifacts/w43/ci-initial.txt`. This worktree's recorded run exists; no
hatch needed anywhere in this arc.

---

## Wave 1 — the instrument first: replay env v2 + enum String bodies

Landed BEFORE the frontend slices, deliberately: the rendered tier's
go-run half (mirror output vs upstream's recorded expectations) is
frontend-independent, so it validates the MIRROR against the external
oracle before any machine work — the strongest available check on the
instrument that will then judge the frontend.

**1a. `tracereplay.py` v2 + `replayenv.go` v2** (items 2+3
infrastructure). The env now mirrors upstream `rafttest`'s OUTPUT, not
just its state transitions: per block, the same string upstream's
`Handle()` returns ("ok" iff the output buffer is empty; handler errors
appended). Pieces:

- **The recording logger (JC-30).** A mirror of `RedirectLogger`: level
  names DEBUG..NONE, the level gate, printf's trailing-newline rule,
  NONE suppressing handler writes too, `log-level`'s case-insensitive
  match (`strings.EqualFold` — the first go-side run caught my
  case-sensitive version: every `log-level none` block answered the
  error string; mirror bug, fixed). SHARED across the env's nodes like
  upstream's, and REPLAY-ENV-ONLY: the twin keeps its stateless logger —
  this env is sequential measurement tooling and makes no §6
  shared-nothing claim (the W4.2 handoff's "per-node" alternative is
  moot here; recorded as the JC).
- **Latent mirror divergences #1 and #2 RETIRED** (both recorded-not-
  fixed in W4.2; the rendered tier is exactly the "moment the subset
  grows" their records named): `splitMsgs` now carries upstream's
  `!(drop && isLocalMsg(msg))` guard verbatim, and `deliver-msgs` walks
  ONE ordered recipient list with per-recipient Drop flags in
  argument-position order.
- **Conf-change support (item 2):** `propose-conf-change` (v1= and
  transition= args, body parsed by the subject's own
  `ConfChangesFromString` — the stepLeader Unmarshal path end-to-end),
  the apply path's `ApplyConfChange` dispatch, AND the piece that made
  the traces agree: upstream's **History appender-state-machine +
  `snapOverrideStorage`** are LIVE in conf-change traces (the leader
  sends the new node a snapshot whose content is History's last, and
  the follower APPLIES a snapshot from Ready) — witnessed by the
  first run's divergences (`sent snapshot[index: 2` vs `4]`,
  `(Non-Voter)` vs `(Voter)`, a refused conf change rendering as
  `EntryNormal ""`), all of which vanished when the History mirror
  landed. `processReady` now mirrors `processAppend` exactly
  (HardState, then snapshot XOR entries — the snapshot-in-Ready STOP is
  retired with the reason above).
- Three channels scored: ok-tier, machine/byte tier, RENDERED tier
  per family (families = `tracefamilies.py`'s command-anchored map,
  imported so the two instruments cannot drift apart).

**1b. plainpb enum `String()` bodies** (`derive.py`): the four enum
types' String stubs become REAL bodies — `_name` map lookup + a decimal
fallback helper mirroring the protobuf runtime's `EnumStringOf`
(fallback unreachable for every value the name maps carry; the file
stays import-free). This REMOVES the W2 stub delta rather than adding
one; message-typed `String()` stubs stay panic stubs (proto text format
— no trace needs it, `Describe*` exists precisely to avoid its detrand
instability). `derive.py --check` clean; `sweep.py` reproduces the
post-swap census EXACTLY (24 quarantined / 5 LIVE / 46 imported stubs
(2 LIVE) / 7 residual sinks — enum String bodies were never census
entries, and the change moves nothing).

**THE GO-SIDE RESULT (the mirror vs the external oracle), whole suite:**

```
28 traces, 558 blocks; supported-prefix blocks: 354 (63.4%)
OK-TIER:       206/206 ok-expectation blocks agree
RENDERED-TIER: 148/148 rendered-expectation blocks agree byte-for-byte
  every family 100%: ready dumps 70/70, pure log lines 35/35,
  raft-state 14/14, status 10/10, raft-log 9/9, message describe 8/8,
  other/mixed 2/2
```

(artifacts/w43/rendered-go-side-{pre,post-enum,post-hist}.txt — the
three-step progression: 48/148 with the mirror alone, 129/148 with enum
Strings, 148/148 with the History mirror.) The supported prefix grew
268 → **354 of 558 blocks** (conf-change unblocked the 11
"multi-line command input" stoppers). Under `go run` the mirror now
reproduces upstream's recorded output byte-for-byte on EVERY supported
block. What this does NOT yet say: anything about the machine — the
machine tier re-runs after the item-1 frontend slices land.

Scope note: the machine tier of this instrument is exercised at wave 4;
nothing in wave 1 touches GoCore, the frontend, `Corpus/` or
`baselines/`.
