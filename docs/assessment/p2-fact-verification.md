# Phase 2 — fact verification of the phase-1 lane reports

Independent re-derivation of the 13 load-bearing factual claims that
will anchor phase-3 headline conclusions. Every number below was taken
from a primary source (data file, tool source, live command) — the lane
reports were not used as evidence for any figure.

- Worktree: `.claude/worktrees/fidelity`, branch `fidelity-assessment`
- Tip: `68045b62` (`park/reasoning-2026-08-31` = `7440bf70`)
- Oracle: `go version go1.26.5 linux/amd64` (matches `baselines/go-oracle-pin`)
- Scratch (gitignored): `artifacts/p2probe/`, `artifacts/verif/`,
  `artifacts/fidelity-claim10/`
- Read-only except this file. No tracked file was modified.

## Verdict summary

| # | Lane | Claim | Verdict |
|---|---|---|---|
| 1 | E | membership: 441 enumerated / 45 exhibited (10.2%); 300/1 at append-spill-size-class | **ADJUSTED** — numbers exact; two phrasings wrong |
| 2 | E/D6 | decoder fail-open defaults for `for` cond and make-chan cap | **ADJUSTED** — behavior confirmed, "fail-open" mischaracterized |
| 3 | E/D7 | `GoVersion` unset ⇒ ambient toolchain's language version | **ADJUSTED** — worse than claimed, and the mechanism is different |
| 4 | E | 249 catalogued frontend obligations, 0 discharged | **CONFIRMED** — and the "0" is vacuous by construction |
| 5 | A2 | negative runner never invokes any GoLean tool | **CONFIRMED** |
| 6 | A2 | ledger §8 "zero unmapped reds" false; 172 vs 169; HIGH at exit 0 | **CONFIRMED** |
| 7 | A1/C/E | `Frame.allocatorIndependence` and `FairStream` absent at tip | **ADJUSTED** — one confirmed, one refuted, framing incomplete |
| 8 | A2 | BUG-062: 5 silent wrong answers, open since 2026-08-19 | **CONFIRMED** — reproduced live (machine 5, gc 1) |
| 9 | A3 | shim surface ~21 fns / 2 shadow types / ~45 decls / ~3,300 lines / 5 mechanisms; [USER] retire-at-second ruling | **CONFIRMED** |
| 10 | B | stdout outside the observation channel; three-layer refusal stack | **ADJUSTED** — sub-claim B needs correction |
| 11 | B | grossmith campaign 2: 79,800 / ~72 min / 1+3+1; arch386 870/4000, 100% in-tag | **CONFIRMED** |
| 12 | A1 | B3 deferral premise refutable by a `defer print` probe | **REFUTED** — probe run; the hypothesis does not survive |
| 13 | C | census MIRROR drift (`resumeThread` 331→402, `l2Entry` 2799→2802) | **ADJUSTED** — drift real and worse; no guard exists |

---

## 1. Membership lane: 441 / 45 / 10.2% — ADJUSTED

**The headline numbers are exact.** Re-derived by summing the raw
per-row artifacts (`artifacts/coverage/membership/<id>/observations.txt`
and `unexhibited.txt`), not the summary line, and cross-checked against
the gate's own detail strings in `artifacts/coverage/latest.tsv`. Two
independent derivations agree:

- rows = **25** (independently confirmed from the tracked corpus
  manifest: `awk -F'\t' '$7=="membership"' … | wc -l` → 25)
- enumerated = **441**, exhibited = **45**, unexhibited = **396**
- 45/441 = **10.204%** → 10.2% ✓
- `slices/append-spill-size-class`: `enum-stats.txt` records
  `observations=300 … leaves=300`; `observations.txt` = 300 distinct
  integers 101…400; `unexhibited.txt` = 299; exhibited = 1 (the value
  224). **300 / 1 / 299 ✓**

The width is not asserted — it is derivable from the model: the choice
site is `Choices.consumeAt .appendSpill width` at
`GoLean/GoCore/Machine.lean:945-948`, with `appendSpillWidth oldCap
newLen = appendSpillUpper - newLen + 1` and `appendSpillUpper = max 32
(2 * appendGrowthCap)` at `GoLean/GoCore/Ops.lean:1964-1969`. For
`oldCap=100, newLen=101`: `max(32, 400) - 101 + 1 = 300`. ✓

**Adjustment 1 — "have ever been observed in Go" overstates it.**
"Exhibited" is per-run state, recomputed each gate run by member line
number at `scripts/diff-coverage:1245-1266`, written to a gitignored
artifact. There is no cumulative record. The correct reading is
"observed by *this run's* samples". It is explicitly metadata, never a
pass criterion (`scripts/diff-coverage:1277-1287`).

**Adjustment 2 — "one Go sample per gate run" is literally wrong; it is
two draws yielding one distinct value.**
`Corpus/coverage/exec/slices/append-spill-size-class/cases.tsv:2`
declares `samples=1`, but the harness runs the sample loop twice, once
plain and once under `-race` — `scripts/diff-coverage:1062-1069`:

```bash
for mode in "" "race"; do
  for ((i = 1; i <= samples; i++)); do
    if ! sample="$(membership_go_observation "$mode")"; then
```

`samples.txt` has 2 lines (both value 224). The substantive point — one
distinct Go observation against 300 modeled members — survives intact.

**Two further caveats phase 3 should carry:**

- The 441 is the sum over **24** rows. The 25th,
  `sync/atomic-frontier/mp-litmus`, FAILS outright (`enumerator failed
  (exit 1; coverage not certified): … unsupported: frontend-quarantined:
  package-selector call atomic.StoreInt32`) and contributes 0.
- **300 of the 441 (68%) are a single row's capacity envelope.** The
  aggregate ratio is dominated by one `append` spill-width site, so
  "10.2% of the model's behaviors have been seen" is not a uniform
  statement about the semantics.
- Enumeration width `B` is **author-asserted per row**, not mechanically
  certified against the site's real bound; the design note records
  mechanical bound certification as explicitly deferred
  (`docs/2026-08-04_membership-lane-design.md:107-113`). For the
  size-class row the assertion happens to be checkable and correct
  (above), but the mechanism does not guarantee it in general.

## 2. Decoder defaults in `GoLean/NativeToIR.lean` — ADJUSTED

**The decode behavior is exactly as described. The "fail-open" label is
not supportable.**

The two sites:

- **for-loop cond** — `GoLean/NativeToIR.lean:1179-1181`:
  ```lean
  let cond ← (match obj.get? "cond" with
    | some c => decodeExpr s!"{path}.cond" c
    | none => pure (.boolLit true))
  ```
  Missing `cond` ⇒ `true` ⇒ infinite loop. Confirmed.
- **make-chan cap** — `GoLean/NativeToIR.lean:669-671`: missing `cap` ⇒
  `none`, and `GoLean/GoCore/Machine.lean:796-798` maps `none` to
  capacity `0` (unbuffered). Confirmed.

**But both are the faithful readings of the emitter's own encoding, and
the emitter omits the field exactly when Go's grammar omits it.**

- `tools/nativefrontend/emit.go:3349` emits `node["cond"]` under `if
  st.Cond != nil` — i.e. `cond` is absent precisely for `for {}` /
  `for ; ; post {}`, which *are* infinite loops in Go.
- `tools/nativefrontend/emit.go:8483-8490` emits `node["cap"]` under
  `if len(c.Args) >= 2` — i.e. `cap` is absent precisely for
  `make(chan T)`, which *is* unbuffered in Go.

Verified empirically. A probe program (`artifacts/p2probe/wire/main.go`)
containing `make(chan int)` and `for { … }`, run through the real
frontend, produced:

```
make-chan keys: ['elem', 'stmt', 'target'] -> cap present? False
for-node keys: ['body', 'stmt']            -> cond present? False
```

So these are **optional fields with semantically-correct defaults**, not
absorbing fallbacks that make an error disappear. Decoding them to a
refusal would reject every `for {}` and every unbuffered channel in the
corpus.

**The residual that IS real, and is narrower than the claim:** the wire
statement grammar has **no exact-key discipline**. `NativeToIR.lean`
contains zero uses of `requireExactKeys`/`exactKeys` (grep count: 0),
unlike the observation decoder (`GoLean/CLI.lean:406,416` +
`GoLean/StrictJson.lean:13-20`). So on a *statement* node, an extra key
is ignored and a missing optional key silently takes its default. The
decoder therefore cannot distinguish "the emitter meant `for {}`" from
"the emitter, or a transport, dropped the `cond` field" — a corrupted or
truncated node degrades to a legal program instead of a loud refusal.
Unknown statement *kinds* do fail closed (`NativeToIR.lean:859`:
`fail s!"unsupported statement {other} at {path}"`), so the exposure is
confined to key-level corruption within a known kind.

**Upstream guards:** `scripts/check-frontend-pins` pins the raft
subject's lowering bytes, and the differential corpus would catch a
dropped `cond` on any covered shape. Neither is a structural guard on
the wire schema itself.

**Corrected fact for phase 3:** *the decoder treats `cond` and `cap` as
optional with Go's own defaults, which is correct; the defect is the
absence of exact-key validation on statement nodes, which removes
loudness under wire corruption — a robustness gap, not a semantic
fail-open.*

## 3. Frontend `go/types` language version — ADJUSTED

The conclusion (no language-version pin reaches the frontend) holds, but
two of the three mechanism statements are wrong and the real failure
mode is worse.

**(a) `GoVersion` unset — CONFIRMED.** Only two non-test `types.Config`
values exist, both zero-valued apart from `Importer`:
`tools/nativefrontend/load.go:644` (`conf := types.Config{Importer:
imp}`) and `tools/nativefrontend/importedmodel.go:279`. `GoVersion` has
zero hits in `tools/nativefrontend/` outside tests.

**(b) The claim's "so the enforced version is the ambient toolchain's"
is WRONG — it is *no version checking at all*.**
`/usr/local/go/src/go/types/api.go:127-132`: *"an empty string disables
Go language version checks."* Confirmed downstream at
`go/types/version.go:55-57` (`allowVersion` returns
`!check.version.isValid() || …`). There is no go.mod fallback: `go/types`
never reads go.mod, and the frontend always runs with `GO111MODULE=off`
(`scripts/diff-coverage:569`, `scripts/check-frontend-pins:47`). The
*ceiling* is the toolchain's implemented feature set (go1.26.5); there
is **no floor**.

**(c) "never evaluates build constraints" is PARTLY WRONG.** `go/build`
and `go/build/constraint` are not imported, but `go/parser` parses
`//go:build` *version* directives unconditionally
(`go/parser/parser.go:158-162` → `ast.File.GoVersion`), which `go/types`
honors as `max(fileVersion, go1.21)` (`go/types/check.go:399-412`). So
**file-level version directives ARE enforced; tag constraints are NOT.**

**(d) The pin that exists is a toolchain-binary pin, not a language
pin.** `baselines/go-oracle-pin` → `go1.26.5`, hard-failed by
`scripts/ci:167-180`. The project already records the gap:
`docs/spec-sources.md:21-25` — *"the corpus has no `go.mod`, so 'the
corpus's `go` directive must agree' has no object today."*

**(e) Two live divergences, measured** (probes under `artifacts/verif/`,
invoked as `GO111MODULE=off go run ./tools/nativefrontend --dir <d> --out <w>`):

| probe | source | frontend | `go run` oracle |
|---|---|---|---|
| p5 | `main.go` calls `helper()`; `extra.go` carries `//go:build ignore` | **accepted, wire emitted** | `undefined: helper` (build error) |
| p7 | loop-var capture + `//go:build go1.21` | emits the go1.22 **per-iteration** desugar ⇒ **3** | **9** (shared loop var) |

p5 is a silent fail-open: a program the oracle refuses to compile is
accepted and lowered. p7 is a semantic divergence: `go/types` honors the
`go1.21` tag for legality, but the emitter never consults
`types.Info.FileVersions` (zero hits in `tools/nativefrontend/`) and
applies the ≥1.22 lowering unconditionally
(`tools/nativefrontend/emit.go:1899`, `:3399-3466`) — precisely the
hazard `docs/spec-sources.md:20-21` names as *"language version is
semantics, not packaging."*

Current exposure is narrow: exactly one non-`deps/` Go file carries a
`//go:build` line (`raftsubject/raft/state_trace_nop.go:15`), whose
excluded twin is not vendored.

**Corrected fact:** *`GoVersion` is unset on both `types.Config` sites,
which per go/types disables language-version checking entirely (not
"falls back to the toolchain"). The toolchain IS pinned to go1.26.5, so
the feature ceiling is go1.26 and there is no floor. `//go:build`
version directives are enforced via `go/parser`; tag constraints are
never evaluated; and the emitter ignores per-file versions — yielding a
demonstrated fail-open (`//go:build ignore` accepted) and a demonstrated
wrong answer (go1.21-tagged loop capture: frontend 3, oracle 9).*

## 4. 249 catalogued frontend obligations, 0 discharged — CONFIRMED

**The catalogue** is `docs/2026-08-21_w7-desugar-inventory.md` (3,367
lines). There is no tsv/json (`git ls-files | grep -i obligat` → empty).

**249 re-derived, not trusted.** Rows are bold headers (`**A-1 · …**`)
except §9.2 where 18 live in a markdown table:

```
bold row headers: 231 ; J table rows: 18 ; TOTAL: 249 ; distinct ids: 249
```

Per-chapter from the bold headers alone reproduces every subtotal in the
document's own table at `:3310` (A 10 / B 45 / C 44 / D 13 / E 36 /
F 15 / G 35 / H 6 / J 27+18=45).

**"Discharged" has no column, no mechanism, and no defined shape.** The
row schema (`:55-74`) carries exactly six fields — Does, Anchor, Spec,
Must preserve, Guardrails, S/M/L. No status, no discharge, no
proof-state. The catalogue's own definition of a row (`:17-19`):

> "Each row is a future **translation-validation proof obligation**: the
> thing a per-program simulation certificate would have to discharge."

The certificate mechanism does not exist — and not merely as unwritten
code. §12 (`:3199-3296`) is six open design questions that must be
answered before a single certificate can even be *stated*: whether
simulation is end-to-end / two-stage / stage-2-trusted (12.1, noting
option (b) "needs a *third* semantics nobody has written"); how the spec
side represents evaluation-order latitude, which if answered wrongly
makes all 13 K2 rows "a certificate that freezes a gc-pin as a fidelity
claim" the doctrine forbids (12.2); shims (12.3); quarantine stubs
(12.4); layout (12.5); go/types re-derivation (12.6). §11 is titled
"**Proposed** order for the **first** translation-validation targets."
The prerequisite tool is absent: `docs/roadmap.md:373-380` records
SpecTec-Go as external and unshipped; `git ls-files | grep -i
"spectec\|transval\|translation"` returns only a prior-art note.

**So "0 discharged" is correct and the column is vacuous** — not "0 of
249 attempted" but "the procedure that would produce a nonzero number
has not been designed, let alone built."

**One nuance in the other direction.** The census describes a second,
weaker sense of discharge that HAS been exercised: converting an
unchecked emitter obligation into a *boundary-discharged free lemma* by
making the Lean decoder fail closed. §11 Tier-0 uses the phrase
(`:3105-3106`); §9.5 lists ~20 invariants "the decoder already
discharges" (`:2883-2903`); and **J-1 is explicitly marked discharged**
(`:2689-2696`) while still counted in the 249. A scrupulous statement is:
*0 discharged by the certificate mechanism the catalogue defines — which
does not exist — with one row (J-1) closed at the decoder boundary
instead.*

## 5. The negative corpus has never been seen by the frontend — CONFIRMED

`baselines/negative-full.tsv:2`:

```
# recorded: 2026-08-18  commit: f68a4d86+ (spec-truth P3 slice 2)  oracle: go build (rejection) + frontend fail-closed
# manifest_cases: 390  pass: 390  fail: 0
```

`scripts/coverage-negative` read end to end (125 lines). Its entire
oracle is two steps:

- `:102` — `if output="$(run_with_timeout … go build -o "$binary" "./$go_dir" 2>&1)"; then report_negative_fail … "program unexpectedly compiled"`
- `:107` — `if [[ "$output" == *"$expected_substring"* ]]; then report_negative_pass`

That is the whole loop. There is **no** invocation of `lake`, `lean`,
`golean`, or `tools/nativefrontend` anywhere in the file (grep for
`golean|GoLean|lake|nativefrontend|lean|frontend` matches only `mktemp`
paths and the `cleanup` function name). `scripts/coverage-negative-manifest`
likewise invokes no GoLean tool (same grep: zero hits). `scripts/ci:514`
runs only `./scripts/coverage-negative`.

**The second conjunct of the header — "+ frontend fail-closed" — is
false. The 390 negative programs have never been passed to the
frontend.** The baseline records 390/390 PASS on an oracle that is
`go build` alone, so the file's own provenance line overstates what its
green means.

## 6. Ledger §8 "zero unmapped reds" — CONFIRMED

Re-ran the reconciler at tip:

```
$ ./tools/reconcile-records
baseline            2478 cases  2306 PASS  172 FAIL
[01] C4  HIGH  the language-coverage ledger §8 arithmetic is computed over a STALE baseline:
      §8 says 2462 cases / 2293 PASS / 169 FAIL; the tracked baseline at this tip is
      2478 / 2306 / 172 (delta: 16 cases, 3 reds). §8 claims 'every one on a named row'
      — that claim is not re-derivable at this tip.
      docs/language-coverage-ledger.md:441
[02] C4  HIGH  §8's red buckets account for 169 reds; the baseline at this tip has 172
      — 3 red(s) are NOT on a named row at the current tip (the §8 invariant
      'zero unmapped' does not hold as written)
3 finding(s).
$ ./tools/reconcile-records >/dev/null 2>&1; echo $?
0
```

**172 vs 169, 3 unmapped, HIGH, exit 0 — all confirmed.**

**The 3 unmapped are the BUG-062 min/max rows — confirmed.** The
baseline carries them as FAIL at `baselines/native-full.tsv:153-155`
(`builtins/min-max-vs-call-order/{min-value,max-value,min-arg-panic}`),
and `docs/language-coverage-ledger.md` contains no
`min-max-vs-call-order` row at all (grep: zero hits).

**Provenance of the divergence.** §8's arithmetic is pinned to
"2462 cases, 2293 PASS / 169 FAIL … recorded 2026-08-22 at `56a12142`"
(`docs/language-coverage-ledger.md:437-439`). The three min/max reds
entered the baseline on the same day in a later commit — `1730567a`
(2026-08-22), *"Baseline re-pin: +13 ids from the launch-audit fix round
(2475 = 2303 PASS / 172 FAIL)"*. So the invariant broke on 2026-08-22
and has stood broken for nine days. **Confirmed.**

**Exit 0 is by design, with an opt-in escape.** `tools/reconcile-records:9`
— *"Deliberately NOT in scripts/: this is an audit instrument, not a
gate"*; `:22` — *"Use `--strict` to exit 1 when any finding is
emitted."* Fair to note phase 3: the tool CAN fail closed, but nothing
invokes it with `--strict`, and nothing invokes it at all — `grep -rn
"reconcile-records" scripts/ .github/ Makefile` returns no hits, and it
is not among `scripts/ci`'s steps. The HIGH finding has therefore been
emitted to nobody.

**Irony worth recording:** the §8 text itself (`:437-441`) documents the
*previous* instance of exactly this failure — *"the arithmetic below had
been vintage-locked to the slice-6 tranche-B baseline … while seven
re-pins moved beneath it, so §8 asserted 'every one on a named row …
zero unmapped' over a red set 40 cases smaller than the real one."* The
2026-08-22 re-derivation fixed the instance and not the mechanism; it
re-broke the same day.

## 7. `Frame.allocatorIndependence` and `FairStream` — ADJUSTED

**Split into two sub-claims with different answers, and the framing
omits a decisive fact.**

**`Frame.allocatorIndependence` — CONFIRMED absent at tip.**
`git grep -in "allocatorIndependence" -- '*.lean'` → rc=1, no output
(filesystem check including untracked/ignored files agrees). At tip it
survives only as prose. On `park/reasoning-2026-08-31` it is a real
theorem, `proofs/GoLeanProofs/Frame/AllocIndep.lean:47`:

```lean
theorem allocatorIndependence {ρ : Nat → Nat} {na₀ na : Nat}
    {σ σF : ExecState} (hS : FrameSim ρ na₀ na [] σ σF)
    {fuel : Nat} {c : Config} {ch ch' : Choices} {out : ExecOutcome}
    (h : execStmtLoop fuel σ c ch = .ok (out, ch')) :
    ∃ outF : ExecOutcome,
      execStmtLoop fuel σF (renameConfig ρ c) ch = .ok (outF, ch')
        ∧ OutSim ρ na₀ na [] (out, ch') (outF, ch') :=
  execStmtLoop_ren fuel hS h
```

with an axiom pin in park's `proofs/Audit.lean:1973-1977`
(`[propext, Classical.choice, Quot.sound]`).

**`FairStream` — REFUTED.** It is not a Lean definition on park either,
nor on any branch:
`git grep -in "FairStream|fair_stream" park/reasoning-2026-08-31 -- '*.lean'`
→ empty; the same sweep across every local branch → empty. It has always
been a **named future-work concept**, and tip docs say so plainly —
`docs/2026-08-06_channels-arc-design.md:79`: *"Later (atomics arc):
`FairStream` — prefix-decidable bounded-starvation predicate…"*;
`docs/language-coverage-ledger.md:416` lists it as a W3.2 open row. It is
cited in 15 tip docs, always as planned work. **No reader is misled about
FairStream, and phase 3 must not pair it with allocatorIndependence.**

**The framing omission: park is an ANCESTOR of tip, and the deletion was
a [USER]-directed repo split.**

```
$ git merge-base --is-ancestor park/reasoning-2026-08-31 HEAD && echo YES-ANCESTOR
YES-ANCESTOR
$ git log --oneline --diff-filter=D -- proofs/GoLeanProofs/Frame/AllocIndep.lean
84fa1e42 Repo split stage 1: main becomes the semantics product only  (Mon Aug 31 2026)
```

Tip has 30 tracked `.lean` files; park has 425. Per
`docs/2026-08-31_repo-split-plan.md` and the worktree charter, the
reasoning product was parked whole for migration to a separate repo.
**The absence is by design, not by accident** — the lane report's
"exist NOWHERE in this repo's tree" is true but reads as loss.

**What IS a genuine defect, and survives the adjustment:** the split
plan's own convention (`docs/2026-08-31_repo-split-plan.md:138-148`)
requires load-bearing citations to carry an explicit
`(branch park/reasoning-2026-08-31)` pointer, and neither of the two
documents that make present-tense proof claims got one:
`grep -n "park/reasoning" docs/2026-08-11_latitude-inventory.md
docs/2026-08-11_essence-of-go-doctrine.md` → **empty**. Those claims are:

- `docs/2026-08-11_essence-of-go-doctrine.md:143-149` (register #6):
  *"Sequential allocation addressing — **DISCHARGED BY QUOTIENT** … the
  executable frame theorem's generalized renaming **proves** every
  conforming address choice observationally equal
  (`Frame.allocatorIndependence` …)"*
- `docs/2026-08-11_latitude-inventory.md:448-459`: *"**UPGRADED
  2026-08-13** … the sequential `nextAddr` allocator is now **PROVEN** to
  be a quotient representative: `Frame.allocatorIndependence` …"*

The reader chasing either hits **three** dead ends: the theorem
(0 `.lean` hits), its supporting note
`docs/2026-08-13_executable-frame-theorem.md` (absent at tip), and its
lemma `execStmtLoop_ren` (0 `.lean` hits). This contradicts the split
plan's own framing at `:166-167` — *"Main makes NO verification
claims"* — main's doctrine register still makes exactly one.
`docs/2026-08-26_mechanism-registry.md`, which carried the `AllocIndep`
row, is also deleted at tip while the project `CLAUDE.md` still points
at it.

## 8. BUG-062 — five silent wrong answers — CONFIRMED, reproduced live

**The dossier** (`docs/BUGS.md:2968-3023`):

- `:2970` — `Status: open`; `:2971` — `Pinned-by: differential`
- `:2972` — `Cases:` lists exactly **5** rows:
  `builtins/len-vs-call-order/{chan,slice}`,
  `builtins/min-max-vs-call-order/{min-value,max-value,min-arg-panic}`
- `:3020-3023` — *"**Owner: mini-slice A6 (queued**, category (a) in
  `docs/2026-08-19_triage-table.md`; queue position in
  `docs/language-coverage-ledger.md`)."* — verbatim ✓
- Opened `3d44b2aa` (**2026-08-19**), *"Slice 6 tranche A: … the
  len-vs-call pin (BUG-062)"* ✓ — **12 days open**
- Forced-point wrong-answer class, stated by the dossier itself
  (`:3007`): *"machine 3 vs go 1 on both pinned rows, a **FORCED-point
  silent wrong answer**"*; widened 2026-08-22 to `min`/`max` with *"a
  silent wrong value (`min(n,100) + bump()` → machine 5, gc 1)"* and
  *"a wrong panic order (`min(b, s[i]), wit(7,9)` → machine 9, gc 0)"*

**All 5 are FAIL at tip** — `baselines/native-full.tsv:138,139,153,154,155`.

**Reproduced live:**

```
$ ./scripts/diff-one builtins/min-max-vs-call-order/min-value
FAIL  builtins/min-max-vs-call-order/min-value  stage=differential
  Lean={"schema":"golean-observation-v1","status":"ok","values":[{"kind":"int","tag":"int","value":5}]}
  Go=  {"schema":"golean-observation-v1","status":"ok","values":[{"kind":"int","tag":"int","value":1}]}
differential coverage summary: cases=1 pass=0 fail=1
```

**Machine 5, gc 1 — exactly the dossier's prediction.** Note both sides
report `status:"ok"`: the machine does not refuse, does not panic, does
not flag. It returns a confident wrong integer. This is the doctrine's
worst failure shape ("a visible red beats a hidden wrong answer") sitting
open for twelve days behind a queued owner.

**Fidelity direction:** this is *observed ∉ modeled* — gc's behavior is
not in the model's outcome set at a **forced** (non-latitude) point, so
no choice-tape quantification rescues it.

## 9. Stdlib-shim injection surface — CONFIRMED

**Line counts (exact):**

```
1459 tools/nativefrontend/stdlibshim.go
 975 tools/nativefrontend/fmtdesugar.go
 413 tools/nativefrontend/fmtcomposite.go
 139 tools/nativefrontend/genericshim.go
 319 tools/nativefrontend/importedmodel.go
3305 total
```

"~3,300 lines across five mechanisms" is exact, and the five are
genuinely distinct mechanisms: allowlist source injection, fmt call
desugar, emit-time composite-renderer generation, generic-callee
dispatch, shadow source models.

**Hand-modeled stdlib functions/methods: 20** (claim said ~21 — off by
one). Counting method: the union of the four dispatch tables in
`stdlibshim.go`, each keyed by qualified stdlib name —
`stdlibShimAllowlist` (`:148-157`, 10: `strings.{Fields,Join,Split,
TrimSpace,Repeat}`, `errors.New`, `bytes.Equal`,
`strconv.{FormatUint,FormatInt,ParseUint}`),
`stdlibGenericDesugarInject` (`:165-169`, 2), `stdlibDesugarInject`
(`:176-186`, 6 fmt entries), `stdlibVarMethodInject` (`:191-199`, 2
`encoding/binary.LittleEndian` methods). Counting the shadow types'
modeled methods too gives 32.

**Shadow types: 2 — CONFIRMED.** `modeledImportedTypes` at
`importedmodel.go:190-209`: `strings.Builder` and `bytes.Buffer`.

**Injected declarations: 45 — exact.** Top-level `func`/`type`
declarations inside `stdlibShimSources` (`stdlibshim.go:244-1265`),
spanning `:269-1248`. Cross-check: the reserved-name collision table
`stdlibShimDeclNames` (`:206-236`) has 43 names; the two missing are the
methods `func (e *goleanShimErrorString) Error()` (`:350`) and
`func (e *goleanShimStrconvError) Error()` (`:975`), which that table's
own comment explains are covered transitively. 43 + 2 = 45.

**The [USER] ruling, verbatim** —
`docs/2026-08-16_overrides-design.md:12-16`:

```
**The user's ruling, verbatim:**

> "fine, but the injection mechanism is a bit of a wart and should be
> retired as soon as we see another instance."
```

Operationalized at `:45-47`:

```
**RETIREMENT TRIGGER — the second shim instance.** The moment a second
library function needs shimming, the injection mechanism is retired in
favour of a **linked registry**:
```

And the document's own prophecy at `:41-43`: *"at ONE allowlist entry it
is legible. At five it would be a small compiler pass nobody designed,
with the injected text as its only specification."*

**The ruling is violated by an order of magnitude and unremediated.**
Threshold 2; current state 20 intercepted entry points across 4 dispatch
tables and 5 mechanisms, 45 injected declarations, 2 shadow types, 3,305
lines — 10× the trigger and 4× the "small compiler pass nobody designed"
mark the document itself named. The prescribed replacement (the linked
registry, `:49-55`) was never built: grep for "registry" in
`tools/nativefrontend/` returns only the unrelated *monomorphization*
collision registry. Source injection at `injectStdlibShims`
(`stdlibshim.go:1269`) is still the live path, called from `main.go:83`.

**Two mitigations for fairness:** the ruling is a *hygiene* decision, not
a trust one — the document says so at `:158-160` (*"nothing in this
section moves when it fires"*) — and each widening did carry the
per-function fidelity argument the document demands (`:162-170`). The
violation is that a mechanism ordered retired at instance 2 was grown to
instance 20 without the replacement ever being built.

## 10. Stdout and the three-layer refusal stack — ADJUSTED

**Sub-claim A — "the harness observes reflected return values, not
printed output" — CONFIRMED.**
`tools/coverageharness/main.go:344-360` generates a `main` that calls the
subject, takes `&_golean_rN` (pointer, to preserve static type), and
passes each to `_goleanObservationValue`; `:376-476`
(`_goleanReflectValue`) is the entire encoder, `reflect.Kind` →
`{"tag":…}`, with no read of stdout anywhere. The corpus program's own
`main` is **deleted** (`:85-87`) and `pruneUnusedImports` (`:97`, `:254`)
strips the now-unused `fmt` — which is why the 187 `fmt.Printf`/`println`
call sites under `Corpus/coverage/exec/**/main.go` are irrelevant (an
enclosing-function scan confirms every one is inside `func main()`).
Stronger: **nothing in the modeled surface can print at all** —
`fmtDesugarFuncs` (`tools/nativefrontend/fmtdesugar.go:104-111`) is
`{Sprintf, Errorf, Fprintf, Fprint, Sprint, Sprintln}` with no
`Print`/`Println`, and builtin `println` is refused at
`tools/nativefrontend/emit.go:2416`.

**Sub-claim B — "stray stdout corrupts the observation JSON and fails
the case" — ADJUSTED.** True for `expected_status=ok`, but there is **no
separation mechanism at all**, and on non-`ok` statuses stray output is
silently ignored rather than corrupting.

The oracle capture is a single combined stream —
`scripts/diff-coverage:475`: `if go_observation="$(go_run_oracle 2>&1)"`.
Program stdout, program stderr, and the harness JSON land in one shell
variable; `go_run_oracle` (`:809-833`) is just `exec go run .` with no fd
separation, sentinel, or buffer swap. What saves it is the strict Lean
re-decode at `:482-483`.

Live probe (scratch corpus, run through the real path):

```
FAIL  stdoutprobe/fmtprint      stage=go-observation  detail=Go output is not a valid observation:
      hello from the program\n{"schema":"golean-observation-v1","status":"ok",…}
FAIL  stdoutprobe/builtinprint  stage=go-observation  detail=Go output is not a valid observation: …
PASS  stdoutprobe/clean
```

Exit code 1. So the outcome is **(iii) a loud parse failure — fail
CLOSED**, not ignored and not mis-parsed. The lenient-parser hazard
(first-value-wins / trailing content ignored) does not exist:
`Lean.Json.parse` enforces end-of-input, so a program cannot smuggle a
spoofed observation ahead of the harness's (`golean observation-eq` with
prepended or appended content → `expected end of input`, rc=2).

**The adjustment:** for `expected_status ∈ {panic, fatal, deadlock,
race}` the compared observation is not parsed from the stream — it is
**synthesized** from substring matches and an awk extraction over the
combined stdout+stderr (`scripts/diff-coverage:492-550`; `panic_message`
at `:104`). On those paths benign stdout is silently ignored. Residual
(theoretical, no working exploit constructed): on a panic-expected case a
subject printing a line beginning `panic: ` would have that line, not
gc's, extracted as the compared message, since `panic_message` takes the
*first* `^panic: ` line. It is unexploitable today **only because no
modeled construct can write to stdout** — a latent coupling to record,
not a live defect.

**Sub-claim C — the three-layer refusal stack — CONFIRMED. All three
refuse loudly; no absorbing default in any of them.**

- **(a) fmt verb-kind matrix.** Verb-parser default arm,
  `fmtdesugar.go:209-210`: `return nil, nil, fmt.Errorf("verb %%%c is
  outside the modeled fmt subset …")`. Terminal verb×type refusal,
  `:825`: *"outside the modeled verb/kind matrix (… fail closed — widen
  with a differential pin first)"*. `fmt.Formatter` pre-refusal at
  `:541-547`. The composite route returns `handled=false`
  (`fmtcomposite.go:60-61`) — **not** a degraded render — falling through
  to `:825`. The dynamic-format route calls `goleanShimUnsupported`
  (`stdlibshim.go:737-757`), which the emitter force-quarantines so it
  throws `GoError.unsupported`, an interpreter-level stop `recover()`
  cannot catch (`stdlibshim.go:119-131`). Live probe with `%X`:
  `frontend-quarantined: fmt.Sprintf format "%X": verb %X is outside the
  modeled fmt subset`.
- **(b) harness encoder.** `tools/coverageharness/main.go:473-475`:
  `default: return nil, _golean_fmt.Errorf("unsupported Go observation
  kind %%s", value.Kind())` — an error, not a fallback value. Named
  refusals: `uintptr` at `:403-404` (deliberately not aliased to
  `uint64`), unnamed-interface dynamic type at `:455`. Live probes
  produced `status:"error"` observations for a map return and a uintptr
  return, which the runner then rejects at `scripts/diff-coverage:485`.
- **(c) strict decoder.** `GoLean/CLI.lean:397-420` pins the schema
  (`:401-402`), switches status with `| other => throw s!"…unknown
  observation status…"` (`:419-420`), and applies `requireExactKeys` on
  every shape (`:406`, `:416`); `:391-392` throws on an unknown value
  tag; `GoLean/StrictJson.lean:13-20` makes `exactKeys` size-equality +
  membership, so an extra key is a refusal. All live probes rc=2, each
  naming its cause.

**One asymmetry worth flagging (not a defect).** The Lean decoder's value
grammar is *wider* than the Go encoder's: it accepts `slice`, `map`,
`mapData`, `addr`/`fieldAddr`/`indexAddr` tags
(`GoLean/CLI.lean:352-390`) that `_goleanReflectValue` can never emit. A
machine-side observation in one of those shapes decodes cleanly and then
fails as an *inequality* at `scripts/diff-coverage:713-714` rather than
as a decode refusal. The direction is safe (the Go side is the strict
one), but "the strict decoder" is not a symmetric filter — the encoder is
the narrower gate.

## 11. grossmith campaign 2 — CONFIRMED

**Note for phase 3: the campaign record lives in THIS repo, not in
`deps/grossmith`.** The primary source is
`docs/2026-08-20_grossmith-findings-2.md` (`deps/grossmith` is the
generator; its own artifacts are gitignored). A first sweep of
`deps/grossmith` alone finds nothing and would wrongly read as
fabrication — flagged here so the phase-3 synthesis does not repeat it.

**79,800 programs — CONFIRMED.** `:59` — *"Main leg
(m1a+m1b+m1c+m2pairs), **79,800 cases, 79,798 reference-ran**"*. Batch
table at `:45-51`: m1a 20,000 + m1b 20,000 + m1c 20,000 + m2pairs 19,800
= 79,800 ✓ (plus a separate `arch386` leg of 4,000).

**~72 min — CONFIRMED with a scope correction.** `:41` — *"Wall clock |
main leg 4 batches, 23:47→00:59 (**~72 min**); legs 2+3 ~25 min"*. The
72 minutes is the **main leg only**; total campaign wall clock is ~97
min. Phase 3 should say "79,800 programs in ~72 min (main leg)".

**Findings 1 machine + 3 gc + 1 latitude — CONFIRMED verbatim**
(`:15-22`): *"79,800 judged programs produced **3 observation mismatches
and 2 reference build failures**. Of those five: **one is ours** (a
forced-point wrong answer that widens open BUG-062 …), **three are gc's**
(one arithmetic miscompilation, two assembler refusals …), and **one is
latitude** … The differential oracle was wrong more often than the
machine was."* Verdict table at `:64-72`: `match` 79,795,
`observation-mismatch` 3, `reference-infra-failure` 2,
`clone-infra-failure` **0**.

**arch386: 870/4000, 100% in-tag — CONFIRMED.** `:453-462`:

```
match 3130 | observation-mismatch 870
cross-arch discrimination: divergences in-tag 870, off-tag 0 over 4000 judged cases
width_dependent-tagged 3493;  width_dependent yield: 870/3493 (24.9%)
```

**Two caveats phase 3 should carry, both from the project's own records:**

1. **The "100% in-tag" figure is weaker than it sounds.** The
   `width_dependent` tag covers 3,493 of the 4,000 cases (87.3%) on this
   leg, and repo-wide `72,353/79,800` (90.7%, `:526`). The generator's
   own backlog says so plainly — `deps/grossmith/TODO.md:217-219`: *"the
   tag saturates at ~98% of programs, so the cross-arch tag-honesty proof
   is **near-vacuous — almost any divergence is in-tag by
   construction**"*; and `deps/grossmith/docs/spec-ledger.md:22`:
   *"in-tag/off-tag is coverage, not specificity."*
2. **The three "gc bugs" are self-classified.** No upstream golang issue
   reference appears in the record, and the campaign's own framing
   inverts the usual direction (`deps/grossmith/BRIEF.md:40`: *"Any
   divergence is a **clone bug**, a declared quotient, or our generator
   bug"*). Phase 3 should write "3 classified as gc defects (not reported
   upstream)".

The zero in `clone-infra-failure` (`:74-80`) is a genuine and strong
result: across 79,798 judged programs the native frontend refused
nothing.

## 12. B3 abort window — the probe, RUN — hypothesis REFUTED

This is the one item where phase 2 was asked to generate missing evidence
rather than check a claim. **The evidence was generated, and it does not
support the phase-1 hypothesis.** Probes: `artifacts/p2probe/*.go`.

### The premise under test

`docs/2026-08-20_w32-boundary-set.md:314-334` (§2 B3, the G1 deferral):

> "A member requiring the panic-window specifically would be partner
> progress strictly AFTER the raise, distinguishable only by
> output-interleaving with the panic message on stderr — **no clean
> oracle observable in our harness**."

Lane A1 (`docs/assessment/lane-a1-register-latitude.md:73-85`) proposed
that a worker running `defer print("A")` before `panic(...)` puts a
"definitionally post-raise" event on stdout, giving a stdout-ordering
observable, and that if gc exhibits it "that is observed ∉ modeled
TODAY."

### The distinction the hypothesis missed

The model has **two** states, not one:

- `.panicking chain k` — mid-unwind, running deferred functions. This is
  a live, steppable thread: `threadDone` (`GoLean/GoCore/Multi.lean:146-155`)
  matches `.panicked _` but **not** `.panicking`, and `MultiConfig.panicMsg?`
  (`:1552-1555`) likewise matches only `.panicked msg`.
- `.panicked msg` — fully unwound, unrecovered. **This** is the abort
  site: `execProgLoop` (`:1616-1619`) tests `match m.panicMsg? with |
  some msg => throw (.panic msg)` *before* stepping.

A deferred `print` runs while the goroutine is `.panicking`. **The model
already interleaves other goroutines with that.** So the proposed
observable lands inside the modeled region, and the B3 window is at
`.panicked`, not at the raise.

*(Citation-drift note, feeding claim 13: the boundary-set note cites
`Multi.lean:1421-1422` for this site; it is at `1616-1619` today.)*

### What was run, and what gc exhibited

**Probe 1 — `b3_natural.go` (the lane report's own design).** Worker
`defer fmt.Fprintln(os.Stdout, "A")` then `panic`; main spins printing
"B". 5 runs, default GOMAXPROCS: **4/5 runs show "B" lines after "A"**
(1, 1, 2, 5 lines). At `GOMAXPROCS=1`, 0/3. So gc does exhibit the
proposed ordering — **but the model does too**, so this is not
observed ∉ modeled.

**Probe 2 — `b3_forced.go` (deterministic handshake).** The deferred
function sends to main and waits for an ack before printing again:

```
A (deferred, post-raise)
B (main, strictly after A)
C (deferred, after partner round trip)
```

3/3 at default GOMAXPROCS and 3/3 at **GOMAXPROCS=1**. gc completes a
full channel round trip with a partner goroutine during unwinding, with
no reliance on parallelism or timing. Again: fully inside the model's
`.panicking` region.

**Probe 3 — `b3_recover.go` (return-value observable).** The deferred
function recovers, so the program exits 0 and the post-raise partner
progress is carried in an ordinary **return value** — inside the
harness's actual observation channel (see claim 10), not the stderr
channel the deferral assumed. 6/6 (`raised=boom;
partner-after-raise=yes`), both GOMAXPROCS settings, exit 0. `recover` is
supported end to end (`GoLean/NativeToIR.lean:199`,
`tools/nativefrontend/emit.go:7768`), so this is a runnable differential
shape. **This does refute the deferral's literal wording** — a clean
oracle observable for post-*raise* progress exists in the harness — but
it observes the `.panicking` region, which is modeled.

**Probe 4 — `b3_postpanicked.go` (the sharp one).** To separate
`.panicked` from `.panicking`: gc's own `panic: boom` traceback is
emitted by `fatalpanic` *after* the goroutine is unrecoverable, so
merging stdout and stderr onto one fd (both unbuffered `write(2)`) orders
partner output against the abort point. Any "B" after the `panic:` line
is progress strictly after the model's abort.

| configuration | runs | runs with partner output after the traceback |
|---|---|---|
| default GOMAXPROCS | 6 | **0** |
| `GOMAXPROCS=8` | 40 | **0** |
| `GODEBUG=dontfreezetheworld=1` | 10 | **0** |

**56 runs, zero exhibitions.** `GOTRACEBACK=all` shows main as
`goroutine 1 [runnable]` — i.e. stopped — in every configuration,
including under `dontfreezetheworld`.

### Verdict and the corrected fact

**REFUTED.** The B3 deferral's substance survives. Specifically:

1. The lane-A1 probe design tests the wrong boundary. Post-*raise*
   partner progress is modeled (`.panicking` is steppable); the B3 gap is
   post-`.panicked`.
2. gc does not exhibit post-`.panicked` partner output in 56 runs across
   three configurations. **No observed ∉ modeled exposure was found.**
   Phase 1's hypothesis is not upgraded to a measured fact; it is
   measured and does not hold.
3. The deferral's literal wording ("no clean oracle observable") is
   nonetheless too strong for the `.panicking` region — probe 3 exhibits
   one in the return-value channel. That is a wording defect, not a
   fidelity defect, because the region it observes is modeled.

**One residual, in the UPPER-bound direction, which phase 3 should carry
instead.** gc's freeze is explicitly best-effort — `deps/go/src/runtime/proc.go:1183-1199`:
*"stopwait and preemption requests can be lost due to races with
concurrently executing threads, so try several times"* (a 5-iteration
loop with `usleep(1000)`), and the `dontfreezetheworld` path at
`:1155-1181` documents that goroutines are deliberately *allowed to
continue execution* after the fatal panic, stopped only when an M
"naturally enters the scheduler." Our probes see nothing because any
partner that produces output must enter the scheduler to do the write —
so the window exists but is **output-invisible by construction**. That is
an implementation-permits/not-observed gap (the doctrine's upper-bound
concern: the model may be narrower than what the machine permits), not
the always-red observed ∉ modeled class. It cannot be closed by
differential testing, which is exactly why B3's disposition should be
argued from the runtime's text, not from probe silence.

## 13. Census MIRROR file:line drift — ADJUSTED

**The census MIRROR** is §0 of `docs/2026-08-11_latitude-inventory.md`
(lines 64-98). Its own framing at `:74-81`: *"**Mirror re-synced
2026-08-22** … The mirror had DRIFTED and nothing was watching it …
**Every row's site is now re-verified** against the
`Choices.consumeAt`/`consumeAtE` call sites at this tip."*

All 9 rows checked against source:

| row | cited | actual now | status |
|---|---|---|---|
| `l2Entry` | `Machine.lean:2799` (`:91`) | **`Machine.lean:2802`** | **DRIFTED** ✗ |
| `appendSpillWidth` | `Ops.lean:1857` (`:90`) | **`Ops.lean:1968`** | **WRONG, 111 lines off** ✗ |
| `mapIter` | StepFn.lean:615–621 | 621 | ✓ |
| `appendSpill` | Machine.lean:946 | 946 | ✓ |
| `l2Arrival` | Multi.lean:853 | 853 | ✓ |
| `l4Waiter` | Multi.lean:1039 | 1039 | ✓ |
| `l1Sched`/`postOp`/`backEdge` | Multi.lean:1153, :1099–1103, :1122–1123 | all match | ✓ |
| `l5ExitWindow` | Multi.lean:1628 | 1628 | ✓ |

Plus, **outside** the mirror table, §C7 at `:317-319`: *"Machine:
`resumeThread` Multi.lean:331–375"* — `def resumeThread` is at
`GoLean/GoCore/Multi.lean:402`. Line 331 today is inside an unrelated
spawn-boundary comment.

**The claim's two specifics:**

- `l2Entry` 2799 → **2802**: **CONFIRMED exactly.**
- `resumeThread` 331 → **402**: **CONFIRMED** on the numbers, but the
  framing is off — this citation is in §C7 prose, **not** in the MIRROR
  table, so it was never in the 2026-08-22 re-sync's scope.
- The claim **understates** the problem: it misses `Ops.lean:1857 →
  1968`, the largest error in the table and the only one landing on a
  wholly unrelated definition (`arithmeticShiftRight`).

**Provenance — one is post-resync drift, one was never true.** At the
re-sync commit `b845c192` (2026-08-22): `Machine.lean:2799` held the
`l2Entry` `consumeAt` correctly (genuine later drift from a 5-line
Machine.lean edit); but `Ops.lean:1857` was **already**
`arithmeticShiftRight`, with `appendSpillWidth` already at 1968, and
`Ops.lean` is byte-identical since. So the document's own assertion at
`:81` — *"Every row's site is now re-verified"* — **was false at the
moment it was written**. `Multi.lean` is likewise unchanged since the
re-sync, so §C7's `331–375` was stale before it too.

**Guard? — NO GUARD EXISTS.**

The only mechanism aimed at this table is `check_choice_sites` (C12) in
`tools/reconcile-records:800-836`, which compares the **row count** to
the `ChoiceSite` constructor count and nothing else. Its own comment
concedes the gap (`:832-834`): *"The table's rows are prose names, not
constructor names, so a name-level match is not available; the row COUNT
is the honest signal."* It parses no `file:line` token; it passes
vacuously today (ctors 9, doc_rows 9). Three further reasons it cannot
catch this:

1. **It is not a gate** — `tools/reconcile-records:9` (*"an audit
   instrument, not a gate"*), `:20-22` (exit 0 whatever it finds).
2. **It is never invoked** — `grep -rn "reconcile-records" scripts/
   .github/ Makefile` → no hits; not among `scripts/ci`'s steps.
3. **No other script checks line citations** — `grep -rln "lean:[0-9]"
   scripts/ tools/` → empty. The only citation lint in `scripts/ci` is
   `scripts/check-spec-anchors` (`scripts/ci:309-310`), which resolves
   `spec#`/`mem#` anchors against the pinned Go spec HTML — a different
   namespace, and it explicitly disclaims content-level drift
   (`scripts/check-spec-anchors:28-32`: *"this lint checks RESOLUTION
   only"*).

The inventory's own 2026-08-22 diagnosis — *"The mirror had DRIFTED and
nothing was watching it"* — holds verbatim nine days later. **A third
instance found by this verification:** `docs/2026-08-20_w32-boundary-set.md:316`
cites `Multi.lean:1421-1422` for the `execProgLoop` panic classification;
it is at `1616-1619` today (see claim 12).

---

## Cross-cutting observations for phase 3

1. **Two claims cited numbers the source does not support in the form
   given (1, 11), and both survived on the numbers.** The failures were
   of *scope wording* ("ever observed" vs this run; "~72 min" for the
   whole campaign vs the main leg), not of arithmetic. Phase 3 should
   quote scope with every figure.
2. **The one hypothesis phase 1 asked to be upgraded to fact was
   measured and did not hold (12).** It failed on a model distinction
   (`.panicking` vs `.panicked`) the lane report did not make. This is
   the strongest argument in the assessment for running probes before
   filing REOPENs.
3. **Three independent instances of uncaught file:line citation drift**
   (claim 13's two, plus the boundary-set note found here), against zero
   guards. The one instrument that could grow into a guard
   (`tools/reconcile-records`) is not wired into `scripts/ci` at all and
   exits 0 by design — which also means claim 6's HIGH finding has been
   emitted to nobody for nine days.
4. **Two provenance lines overstate what a green certifies**:
   `baselines/negative-full.tsv:2` ("+ frontend fail-closed", claim 5)
   and `docs/2026-08-11_latitude-inventory.md:81` ("every row's site is
   now re-verified", claim 13). Both are self-descriptions of scope, and
   both are false as written.
5. **The refusal machinery, where it exists, is genuinely fail-closed**
   (claim 10: all three layers refuse loudly, with no absorbing default
   in any of them; claim 2: unknown statement kinds fail closed). The
   gaps found are gaps of *coverage* — no exact-key discipline on
   statement nodes, no language-version floor, no negative-corpus
   exposure — not of doctrine.
