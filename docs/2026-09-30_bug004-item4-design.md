# BUG-004 item 4 — the abort line of an `error` / `fmt.Stringer` payload: design (2026-09-30)

[AGENT] design writer, lane `docs/bug004-item4-design-0930` (off `main` @ `20049982`). Asked for by the logic team's route-A reply
(`docs/2026-09-30_note-from-logic-team-route-a.md` §4); posed by `docs/2026-09-30_protobuf-route-a.md` C3. Inputs: `docs/BUGS.md` BUG-004
(`:2854`; item 4 `:3077`), the abort path (`GoLean/GoCore/{Machine,StepFn,StringPanic}.lean`), packet A/B (`ExecutionStatement.lean`,
`Prefix.lean`, `BridgeSet.lean`), gc's runtime at the pin (`deps/go/src/runtime/panic.go`, go1.26.5), 25 probes under the pinned toolchain
(`docs/evidence/2026-09-30_bug004-item4-design/probes.md`, cited `pNN`). Records only; nothing is decided — §5's decisions are PENDING [USER].
**[inf]** marks an inference; every other claim is source- or probe-anchored.

## 0. In one paragraph

gc does not render an `error`/`Stringer` payload: it CALLS the method — after every deferred call, before anything prints, before the world
stops — then prints the returned STRING like any string payload. The faithful fix has the same shape: a PREPRINT PHASE of ordinary machine steps
runs each pending payload's method (newest first, skipping what gc skips) and stores the text beside the payload; the abort configuration becomes
«a chain with no pending rewrite», to which today's one-step render applies unchanged. `Finish` stays a cost-1 terminal, the packet A/B statements
keep their text, `stepFn` stays total, no new choice site. A whitelist renderer (ii) is faithful only for `return "literal"` bodies — the two red
pins and nothing raft needs. Recommended: (i), ≈3.5–5 sessions, inside the window after C4 and before packet D (after the offer = a second re-pin).

## 1. gc's exact behaviour (runtime source at the pin; probes)

- **When.** `gopanic` (`panic.go:809`) runs every deferred call (`:856`), then — «Because it is unsafe to call arbitrary user code after
  freezing the world» — `preprintpanics(&p)` (`:877`), then `fatalpanic` (`:879`: `freezetheworld` `:1538`, `printpanics` `:1473`). So the
  methods run on the panicking goroutine, after ALL its defers, before any output, with the world still running: a goroutine spawned inside
  `Error()` completes a channel round-trip (p15; p24); `Error()` sees post-defer state (p08: `after`); a RECOVERED panic's method is never called (p09).
- **Which, in what order.** `preprintpanics` (`:702`) walks the chain NEWEST → oldest. Per entry: if its OLDER neighbour holds the identical
  eface (`*efaceOf(&p.link.arg) == *efaceOf(&p.arg)`, `:715`) it marks the older `repanicked` (`:718`) and SKIPS this entry — no call, and
  `printpanics` (`:737`) never prints it; else `case error: p.arg = v.Error()` (`:723`), `case stringer: p.arg = v.String()` (`:725`) —
  `error` wins (p01); the runtime's own two interfaces: any `Error() string`/`String() string` qualifies, a wrong signature does not (p18:
  `main.T(3)`, `main.U(4)`); promoted methods count (p19). Method sets as everywhere: a `*T` payload has `T`'s value methods (p06), a `T`
  payload lacks `*T`'s (p07: `main.Q(3)`; the struct prints `(main.P) 0x497da8` — an ADDRESS, the standing refusal class). Calls are
  newest-first (p10: `CALLED:second`, `CALLED:first`, then `panic: first [recovered]` / `\tpanic: second`) and their COUNT rides on the identity
  decision (p11 same box: one call, `[recovered, repanicked]`; p11b re-boxed small int: two calls, two-line form; p12 two `E{"x"}` literals:
  one call — static dedup; p21 an UNRECOVERED equal pair: one call, `panic: same`, no suffix) — item 1's latitude, now with a call count.
- **Then** `printpanicval` (`error.go:215`) prints the rewritten arg as a STRING via `printindented` (first line at the first LF — p20); the
  suffix rule (`:750`/`:752`) is unchanged. `panic(nil)` → `*PanicNilError` (`:812`), whose `Error()` (`:794`) is rewritten like any other →
  `panic: panic called with nil argument [recovered, repanicked]` (p13); runtime errors likewise (p23).
- **When the method misbehaves.** A panic out of `Error()`/`String()` is recovered by `preprintpanics`' deferred function (`:703`–`:712`) and
  turned into `throw("panic while printing panic value: " ++ s)` for a string payload, `"…: type " ++ <gc type string>` otherwise — a FATAL,
  exit 2, the original `panic:` line never printed (p02 `inner-string`; p03 `type main.Inner`; p04 nil pointer receiver dereferenced →
  `type runtime.errorString`; p06 value method through a nil `*V` → `panicwrap` → `type runtime.plainError`). A constant-returning method on a
  nil receiver is fine (p05). `recover()` inside the method's own defers sees nothing (p17). `os.Exit(3)` inside → exit 3, nothing printed (p16).
  Blocking with no other runnable goroutine → `checkdead`'s `fatal("all goroutines are asleep - deadlock!")` (`proc.go:6468`) from g0, where
  `printPreFatalDeferPanic` (`panic.go:1259`) has no chain: the bare deadlock line, the pending panic NOT printed (p14). Looping → hangs (p22).
  Races with other goroutines: ordinary Go until `fatalpanic` freezes the world.

## 2. Options

**(i) The preprint phase — RECOMMENDED.**
1. `PanicEntry` (`Machine.lean:3050`) gains `rewrite : Rewrite` and `repanicked : Bool` — gc's own two records (`_panic.arg` overwritten,
   `_panic.repanicked`); `inductive Rewrite | none | pending (m : MemberId) | unrecorded | done (text : GoString)`. The mark is computed at the
   RAISE (`Step.panicRaise`, `Machine.lean:6245`, which has `ctx`) by today's method-set check (`hasNoArgStringMethod` `:3175`,
   `panicPayloadIsRewritten` `:3186` — a static property of the dynamic type, so deciding it early is sound): `pending Error`/`pending String`;
   `unrecorded` for a carrier without a method-set record (BUG-053 — today's refusal, kept, at the ABORT, so recovering it stays supported);
   `none` for string/int/bool payloads and the machine's `runtime.Error` twin (`runtimeErrorValue` already IS gc's rewritten text; `panic(nil)`
   maps there). The text is kept BESIDE the value: gc compares identity on the raw efaces before overwriting, our collapse envelope compares
   original values. Today's literals `⟨v, false⟩` become structure instances (3 in the core; `AbortObservation.lean:20`; tests).
2. `Config.abort?` (`Machine.lean:4354`; type pinned, BridgeSet row 19) keeps its type — no `ctx` needed: `.panicking (first :: rest) .stop`
   with every entry SETTLED (`rewrite ≠ pending _`). A chain with a pending entry at `.stop` is an ordinary RUNNING configuration.
3. `stepFn`'s `.stop` arm (`StepFn.lean:381`–`399`): settled → today's step exactly (consult + `abortMsg`); else the PHASE STEP at the newest
   pending entry `eᵢ`: if its older neighbour `eᵢ₋₁` has an equal value (`==`, item 1's identity question) consult `repanicCollapse` at bound 2 —
   the SAME site, drawn where gc's `:715` compare sits: slot 0 = identical → `eᵢ₋₁.repanicked := true`, DROP `eᵢ` (gc never prints it), continue;
   slot 1 = distinct → proceed; then resolve `m` (`resolveMethod?` `Ops.lean:1061`), adjust the receiver (`receiverAt` `Ops.lean:3554` — a nil
   `*T` under a value method PANICS here as at any dispatch), enter the frame (`enterFramePickV`, `Machine.lean:4300`'s shape) as `.exec body
   fenv (.frame [] [] resultLocs [] [preprintK i chain] fid)`. The consult's record rides in `picks`; the `seqConsumption` arm (`Machine.lean:5714`)
   generalizes from «recovered head with an equal successor» to «this pair» (today's condition at a settled chain).
4. `Frame.preprintK (i : Nat) (chain : List PanicEntry)` — a new frame with its own `FrameClass` (`Frame.class` is exhaustive by design, `:3839`;
   `panicPassthrough` `:3966` stays `none` on it). Result delivery: `stepFrameExit`'s `[], rl :: rls, []` arm — today `.stuck "extra GoCore
   assignment value"` (`StepFn.lean:162`), unreachable — gains the sub-arm «head `preprintK` ⇒ load the one result, `.retV s [preprintK …]`»; the
   `.retV` arm stores `rewrite := done s` into entry `i` and continues at `.panicking chain' .stop`; with no pending entry left the configuration
   IS the abort and today's render runs. **[inf]** two phase steps per method call plus the call's own steps.
5. Rendering: `renderPanicPayload` (`:3205`) keeps its value arms FIRST (string, `runtime.Error`, int, bool — so `renderPanicHead_string`/
   `_runtimeError` and every `StringPanic` statement hold by their present proofs), then `done s ⇒ stringFirstLine? s.bytes` (D5's invalid-UTF-8
   refusal applies unchanged, p20's first-line rule too), then the defined-int `main.T(v)` arm, then `none` — the method-set refusal at `:3239`
   becomes «`pending`/`unrecorded` at an abort» (the standing fail-closed guard; `pending` unreachable there). `repanicEqualNext` (`:3282`)
   additionally requires the head's `rewrite ≠ done _` (a rewritten head's identity was decided in the phase — no second pop); `recoveredSuffix`
   (`:3313`)/`collapseBit` (`StringPanic.lean:28`) read `first.repanicked || (repanicEqualNext … && pick == 0)`. Un-phased chains: unchanged.
6. Failure inside the method: the nested chain unwinds the method's frames as usual (its own `recover` works — p17's shape); on reaching
   `preprintK` a NEW `.panicking` arm raises `.terminal (.fatal ("panic while printing panic value: " ++ t))` — `t` = a string payload's first
   line, `"type " ++ displayName` for a defined type with a display record, else REFUSE by name (one synthetic `runtime.Error` type cannot name
   gc's `runtime.errorString`/`plainError` — BUG-099; p04/p06). `Finish.fatal` (`ExecutionStatement.lean:140`) classifies it at cost 1, exit 2 as
   gc. Blocking → a blocked form inside the phase (sequential `.deadlock` — gc's bare line, p14; under the pool others run); looping → fuel-out.

Consequences. Totality: ordinary steps, no recursion inside a rule. Tape: no new site; `repanicCollapse` drawn once per equal adjacent pair the
walk meets (today once, at the head; a bound-1 consult still pops nothing). Relation: ~4 new `Step` rules (`preprintBegin` skip/enter,
`preprintStore`, `preprintFatal`, the frame-exit delivery) with their `stepFn_sound`/`step_complete` cases. Packet A/B: `Finish`'s five
constructors (`:120`), `finish_abort_step` (`Prefix.lean:385`), `finish_refused_step` (`:165`), `finish_replay` (`:250`), `run_panic_iff` (`:454`),
`boundary_abort_one` (`:280`), `stepFn_no_stray_panic` keep their TEXT — all stated through `c.abort?`/`abortMsg`/`repanicCollapseWidth`; `Finish`
remains the cost-1 terminal; the phase is `Prefix` steps (`run_panic_iff`'s `n + 1 ≤ fuel`, longer `n`). Semantic changes: `Config.abort?`'s
equation (`abort?_some` `Prefix.lean:132` gains the settled conjunct), `stepFn_abort` (`:141`), `stepFn_strict` (`StepErrors.lean:789`) re-proved.

**(ii) Restricted rendering** — a whitelist: body `return <string literal>`, receiver `asIs`, empty path; render the literal at the abort,
refuse otherwise. Faithful ONLY on that class (no state, effect or fault — even the receiver adjustment must be `asIs`: p06 faults before any
body runs). It flips the two red pins (`"boom"`/`"strung"`) and nothing that matters: raft's `panic(err)` payload is protobuf's
`prefixError.Error() = prefix + e.s` and `errors.New`'s `(*errorString).Error() = e.s` — field and global reads. Widening to «pure bodies» is a
second evaluator inside the terminal rule — the charter's «no semantic choice hides in evaluator recursion» — and re-opens the item-2 regression
class (BUGS.md, 2026-07-31 finding 3). Not recommended, not even as an interim. **(iii) Rejected variants:** rewrite at RAISE time (unfaithful —
gc calls only if unrecovered, after all defers: p08, p09); a nested `runConfig` inside `abortMsg` (total, but hides unbounded steps, output,
picks and faults in one cost-1 step and cannot interleave the pool); always calling every pending method with no identity choice (p11/p12/p21).

## 3. Blast radius

- **Trust surface #1** (`GoLean/GoCore/`; `--diff`): `Machine.lean` (`PanicEntry`, `Rewrite`, `Frame.preprintK` + class, `Config.abort?`,
  `renderPanicPayload`/`repanicEqualNext`/`recoveredSuffix`, `seqConsumption`, `Step` +~4, `Step.panicRaise`'s entry); `StepFn.lean` (the
  `.stop` arm split, the `stepFrameExit` sub-arm, the `.retV`/`.panicking` preprint arms); `MachineSound` (+cases); `StateWf` (`panicChainSup`
  `:438` untouched — scalars; the frame's `locSup`/`ownSup`); `StepErrors`, `PrefixFacts` (`stepFn_picks_*` over the new consult arm), `Prefix`
  (`abort?_some`, `stepFn_abort`); `StringPanic` (`collapseBit`; NEW text lemmas); `Multi`/`MultiSound` (the tombstone arm `Multi.lean:1516` via
  `Config.abort?`; `poolConsumption` `:1739`); `EnumDedup.lean` (`contDepth` `:53`), `MachineEqb` (`PanicEntry.eqb` `:407`, `Cont.eqbF` `:424`),
  `AbortObservation`, `NPDRF`/`UnseqSound` literals; `Tests/{PanicRendering,StringPanicMembers,GoCoreContract,GoCoreAudit}.lean`. **Wire: no
  schema change.** Content risk: the phase needs the method's BODY; library units are emitted reachability-pruned (`tools/nativefrontend/
  stdlibreach.go:3`), so a stdlib `Error()` reached only through the payload (`errors.New`'s) may be absent — the phase refuses by name
  (`methodDecl?` none) and the reach set gains «methods of panic-payload types» as a follow-up (wire content, `--slow`). The lane measures this first.
- **BridgeSet.** No pinned STATEMENT changes text; row 19 keeps its type. `Frame` gains a constructor (a client's exhaustive `cases` gains a
  case), `Step` gains rules, `PanicEntry` gains fields (their `⟨v, false⟩` terms break) — CHANGELOG lines (`docs/changelog/61958f2e-WINDOW.md`)
  and a RE-PIN block with the new equations; the core audit's required list (144 at G-C3) grows by them. **Packet D** (its brief's deliverable 1
  «the abort at `.stop`»; addendum F4 frame-exit equations) must be stated over the phase's arms — D after this lane, or D re-opened.
- **Corpus.** `panic-recover/panic-defined-payload-methods/{error,stringer}` (`baselines/native-full.tsv:4548`, `:4551`) FAIL → PASS (strict,
  `boom`/`strung`) and LEAVE BUG-004's Cases line; no other red is item 4 (the other `lean-observation` reds are item 3/D5 and BUG-099). Born from
  the probes, one row each (membership where the pick decides count or suffix): p01, p05, p08–p13, p17–p21, p24; p02/p03 `expected_status: fatal`;
  p04/p06 REFUSED by name (red on BUG-099); p14 deadlock; p07 the address refusal. Route A's D3 twin row (`…protobuf-route-a.md:100`) becomes passable.
- **The logic side.** `Finish.aborted` unchanged in text; the phase's per-step equations (packet D); the rendering equations they asked for —
  `renderPanicHead_text`/`abortMsg_text`/`stepFn_text_abort`/`runConfig_text_abort`, `StringPanic`'s statements with `first.rewrite = done s` as
  the payload premise; plus their own error-payload stage (their §4: 1–3 sessions).

## 4. Size and placement

Sessions ([AGENT], ±50%; precedents: packet C 3–4 for a pure reshape, the L3 rendering chunk): S1 core — fields, frame, arms, renderer,
`Config.abort?` (1); S2 relation and re-proofs — `MachineSound` cases, `StateWf`, `StepErrors`, `PrefixFacts`, `Prefix`, `StringPanic` text
lemmas (1–2); S3 pool/dedup/eqb, ~18 rows, `--diff`, BUGS.md/ledger/latitude R10/changelog (1); audit + fix round (0.5–1): **3.5–5**.

Placement. The lane changes the abort's finishing transition SEMANTICALLY (`Config.abort?`, `PanicEntry`, `Frame`, `Step`, the abort
equations) though no pinned statement changes text, so landing AFTER the offer is a second re-pin of exactly the surface the logic side pins —
against the ONE-re-pin ruling (charter `:160`). Inside the window the slot is after packet C (the frame is a `Frame`), B6 and the `Intn` unit 5b,
after C4 (no allocation is touched, but the frame-exit/result-cell code should be written once over C4's shape), before packet D (equations stated
once): `4 → 5 → 5b → 6 → 6b → 7a`, +3.5–5 on a ≈25–39-session window. The alternative — after the window — leaves the window as ruled; the
logic side excludes error-payload panics by precondition (their §4: acceptable for the end-to-end theorem when the codec contract proves valid
bytes decode with a nil error); route A's D3 witness stays red on C3; the fix lands later with the second re-pin their error-payload stage would
need anyway. **The tradeoff:** window length (+≈15%) vs a second re-pin (breaking `PanicEntry`/`Frame`/`Step`/the abort equations after the
offer) vs fidelity now (every `panic(err)` — raft's own abort path — refused until it lands).

## 5. Decisions for the [USER] (each PENDING; provenance [AGENT] proposal)

1. Design (i), the preprint phase of §2, as the fix for BUG-004 item 4 — RECOMMENDED; (ii) not taken, not even as an interim.
2. `PanicEntry` carries `rewrite`/`repanicked` (gc's two records; mark at the raise, text beside the value) — RECOMMENDED over a frame-only
   encoding: the render stays one step, the pinned statements keep their text, `Config.abort?` keeps its type.
3. Item 1's identity choice drawn inside the phase at EVERY equal adjacent pair (same site, bound 2; the call count is observable, p11/p12/p21) — RECOMMENDED; else a named refusal on non-head equal pairs.
4. The fatal's text for a panic inside the method: exact for string and display-named defined payloads, REFUSED by name for runtime-error
   payloads (BUG-099) — RECOMMENDED over a message-keyed type guess.
5. Placement: inside the window as unit 6b (after C4, before packet D), +3.5–5 sessions — RECOMMENDED; else after the window, with the logic
   side's precondition meanwhile and a DECLARED second re-pin.
6. Owner: Fable for S1–S2, Opus for S3; the audit ask unconditional; G-C3's stop rule (a module > 1.5× slower or a raised `maxHeartbeats` STOPS).
