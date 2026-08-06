# Goose/Perennial concurrency research — goroutines, channels, select, sync (2026-08-06)

Input to GoLean's channels/goroutines arc design note. Format per
`docs/2026-08-04_floats-design.md`: **[FACT]** = verified against a primary
source, cited `file:line@rev` or URL; **[ANALYSIS]** = my reasoning, marked.

Revisions cited (recorded per charter):

- `deps/goose` @ `3be88bbb4982f58e5813b6f0344302d5582c8e8a` (branch `new`; equals
  upstream `goose-lang/goose` head at time of writing). Cited as `goose:<path>`.
- `deps/perennial` @ `43d4efabc22eb148eb239ebee89d1dd2ee54c900` (branch `master`).
  Cited as `perennial:<path>`.
- `deps/iris-lean` @ `3877dbeccd1b0545c5be7ef73318e8c86acf79ab` (not needed below).
- Upstream history inspected from fresh partial clones (worktree scratch,
  `.scratch-clones/{goose,perennial}`): goose upstream head = the pinned rev;
  perennial upstream head `8d5165bf6` (pinned rev is 2 commits behind, both
  dependabot). Historical commits cited by short SHA from these clones.

Headline finding up front: **channels in Goose/Perennial are not language
primitives — they are a generic Go library (`goose/model/channel`) written by
the Goose authors, translated by Goose itself into GooseLang, and verified once
against logically-atomic Iris specs.** The only new machine syntax is
`SelectStmt`. The current model (offer-state-machine, full select support) is
2025–2026 work by Levi Redlin and Tej Chajed, replacing Jessica Zhang's Feb-2025
MEng-thesis model which lacked select. No paper on the new model exists yet; it
is being driven by an in-tree verification of **etcd-io/raft** — the same
north-star target as GoLean.

---

## 1. GooseLang core: the concurrent operational semantics

### 1.1 Language + thread model

**[FACT]** GooseLang is "an adaptation of HeapLang with extensions to model Go",
with an FFI parameter for external ops and crash semantics
(`perennial:src/goose_lang/lang.v:20-30@43d4efab`). NOTE: at this rev the *old*
and *new* semantics have been merged — `lang.v` imports
`New.golang.defn.prelang` (line 14) and contains the Go-specific instruction
layer; the old `goose_lang` files were deleted 2026-01-30 (perennial
`eb748d43e`, "Start deleting old files").

**[FACT]** Threads: standard Iris-style thread pool. A configuration is a list
of expressions plus state; one step picks one thread, runs one `prim_step` of
it, and appends any forked threads to the END of the pool:
`ρ2 = (t1 ++ e2 :: t2 ++ efs, (σ2, g2))`
(`perennial:src/program_logic/language.v:118-122@43d4efab`). Interleaving
small-step; no thread IDs, no scheduler, no fairness, threads are never removed
from the pool.

**[FACT]** `Fork` is an expression constructor (`lang.v:234`); its rule is
`| Fork e => ret ([], Val $ #(), [e])` (`lang.v:1344`) — parent gets `#()`
immediately, `e` becomes a new pool entry. Free/unstructured fork; no join
primitive, no thread handle.

**[FACT]** `go f(args)` translation (`goose:goose.go:1654-1673@3be88bbb`):
`callExprPrelude` evaluates the function value and all arguments **in the
calling goroutine** into `$go`, `$a0…$an` bindings, then emits
`Fork ($go $a0 … $an)` (`goose:glang/coq.go:804`). [ANALYSIS] This matches the
Go spec ("the function value and parameters are evaluated as usual in the
calling goroutine") — a guardrail case worth pinning in our corpus (argument
evaluation happens-before goroutine start; panics in arg evaluation happen in
the caller).

### 1.2 Atomicity granularity (their answer to our BUG-002 concern)

**[FACT]** One atomic step = one head-redex reduction via evaluation contexts
(`ectxi_language`; `prim_step'` at `lang.v:1452-1456`); every case of
`base_trans` (`lang.v:1332-1443`) wraps its state transition in `atomically`,
so each base step's state effect is indivisible. Expression evaluation is
otherwise fully interleavable — sub-expression granularity.

**[FACT]** Non-atomic memory accesses are *deliberately split into two base
steps each* so that races are operationally detectable:

- heap cells carry a mode: `heap : gmap loc (nonAtomic val)` with
  `naMode ::= Writing | Reading (n:nat)` (`lang.v:543-546,626-633`);
- na read = `StartRead` (requires `Reading n`, bumps to `Reading (S n)`,
  returns the value) then `FinishRead` (decrements) (`lang.v:1352-1371`);
  derived form `Read` (`lang.v:371-374`);
- na write = `PrepareWrite` (requires `Reading 0`, sets `Writing`) then
  `FinishStore` (requires `Writing`, installs value, back to `Reading 0`)
  (`lang.v:1380-1396`); derived form `Store` (`lang.v:364-367`);
- any access that finds the cell in a conflicting mode hits `undefined` → the
  thread is **stuck** = UB.

**[FACT]** Primitive atomics (`lang.v:84-105,240,1372-1431`):
`LoadOp` (atomic load — allowed while readers are outstanding, stuck if
`Writing`), `AtomicSwapOp`, `AtomicAddOp` (w64/w32/w16/w8), `CmpXchg`
(ternary; returns `(old, bool)`; only writes when the compare succeeds and
requires zero outstanding readers at that point, `lang.v:1422-1431`), plus
`ArbitraryIntOp` (demonic integer nondeterminism), `PanicOp s` ("a stuck
expression, to represent undefined behavior", `lang.v:85-86`), prophecy ops
inherited from HeapLang. So yes — GooseLang has an explicit na/atomic
distinction, enforced by the `naMode` instrumentation rather than by an access
-mode type system.

**[FACT]** Typed Go loads/stores are built ON the na primitives: `GoLoad` on a
base type unfolds to `Read l` and `GoStore` to `l <- v` (the two-step na
forms), and struct loads/stores decompose into per-field `GoLoad`/`GoStore`
(`perennial:new/golang/defn/postlang.v:496,499-522,511-513@43d4efab`). So an
ordinary Go struct assignment is MANY steps — na and per-field. (The comment
"atomic load (used for most normal Go loads)" at `lang.v:1372` is stale
old-semantics prose; the new `GoLoad` path goes through `Read`.) The `sync/
atomic` package maps to the atomic prims: `Load*→Load`,
`Store*→AtomicSwap ;; #()`, `Add*→AtomicAdd`, `CompareAndSwap*→Snd (CmpXchg …)`
(`perennial:new/trusted_code/sync/atomic.v:8-73@43d4efab`).

**[FACT]** The Go-specific instruction layer (`go_instruction`, `lang.v:161-219`
— `GoLoad/GoStore/FuncResolve/MethodResolve/TypeAssert/SelectStmt/…`) steps via
a *relation* `is_go_step` provided by typeclasses (`go_instruction_step`,
`lang.v:1313-1321`); the channel/select axioms of §2 plug in there.

[ANALYSIS] Their granularity doctrine, stated crisply: *the atomicity of an
access is part of its semantics, and making non-atomic accesses multi-step is
the mechanism that turns racy programs into stuck programs.* This is exactly
the class of decision our BUG-002 taught us cannot be recovered from tests —
they hard-coded it into the state (naMode) rather than into a side judgment.
The design is executable (mode counters update deterministically), which
matters for us: it transfers to an interpreter unchanged.

## 2. Channels

### 2.1 The model: a Go library, goosed into the logic

**[FACT]** `perennial:new/golang/defn/chan.v:1-11@43d4efab` — the channel
"definition" simply imports the *Goose translation of the Go channel model*
(`From New.code.github_com.mit_pdos.perennial.goose.model Require Import
channel`) and defines `chan.send/receive` as `MethodResolve` calls on
`channel.Channel elem_type`'s `Send`/`Receive` methods. `go.make/close/len/cap`
on channel types unfold to `channel.NewChannel/Close/Len/Cap`
(`defn/chan.v:79-93`). The translated model is
`perennial:new/code/github_com/mit_pdos/perennial/goose/model/channel.v`
(930 lines, autogenerated).

**[FACT]** The Go source of the model, `goose:model/channel/channel.go@3be88bbb`:

```go
type Channel[T any] struct {
    cap int
    mu    *primitive.Mutex   // protects all remaining fields
    state offerState         // buffered|idle|sndPending|rcvPending|sndCommit|rcvDone|closed
    buffer []T               // buffered channels only
    v T                      // in-flight value, unbuffered only
}
```

- **Buffered**: `TrySend` appends if `len(buffer) < cap`; `TryReceive` pops
  head (lines 51-59, 125-134). FIFO by construction.
- **Unbuffered**: an *offer protocol*. A blocking `TrySend` in state `idle`
  posts `sndPending` + parks the value, **releases and re-acquires the lock**,
  then either finds `rcvDone` (offer taken → success) or rescinds
  (lines 66-92). `TryReceive` mirrors with `rcvPending`/`sndCommit`
  (lines 151-172). Non-blocking calls never post offers, only accept them
  (lines 90, 173) — that asymmetry is what makes two non-blocking selects on
  opposite ends of an unbuffered channel correctly fail to rendezvous.
- **Blocking ops are spin loops**: `Send = for !TrySend(v,true) {}`,
  `Receive = for { if TryReceive(true) ... }`, `Close = for !tryClose() {}`
  (lines 105-113, 189-201, 228-234).
- **nil channel**: `Send`/`Receive` on nil → `for {}` (block forever, lines
  106-110, 190-193); `Close(nil)` → `panic` (line 229-231); `Len(nil)=0`,
  `Cap(nil)=0` (lines 253, 267).
- **close**: `closed` state keeps the buffer; receives **drain** the buffer
  before returning `ok=false` with the zero value (lines 135-144); close of a
  mid-handshake unbuffered channel waits for the exchange to finish
  (lines 206-221); `close` of closed and send on closed `panic`
  (lines 49-50, 209-210).
- **for-range over a channel**: `Iter()` yields via `TryReceive(true)` loop
  (lines 273-292); the GooseLang side has `chan.for_range` desugaring to a
  receive loop that breaks on `!ok` (`defn/chan.v:13-22`).

**[FACT]** `panic` in the model becomes GooseLang `Panic` = stuck/UB
(`lang.v:85-86`), so *send-on-closed / double-close are proof obligations*
(their close/send AUs literally contain `False` in the `Closed` branch —
`chan_au_base.v:187,205,224,295`), not modeled panics.

**[FACT]** History of the model's shape: Zhang's earlier model (old goose
`master:channel/channel.go`, seen via `git show` in the clone) was a 6-state
machine (`start/receiver_ready/sender_ready/receiver_done/sender_done/closed`)
with a circular buffer and `sync.Mutex`; the current model refactored to
explicit offer states (goose `da51f4a`, 2025-09-03), dropped the `sync`
dependency in favor of `primitive.Mutex` (`4f4d802`, 2025-10-24), and got an
iteration model (`5336bfa`). `primitive.Mutex` is trusted-mapped to a `bool` +
`CmpXchg` spinlock (`perennial:new/trusted_code/github_com/goose_lang/
primitive.v:41-49`, `new/golang/defn/lock.v:7-19`).

### 2.2 Select: the one new machine construct

**[FACT]** Syntax: `SelectStmt` go-instruction + `SelectStmtClauses
(default_handler : option expr) (l : list comm_clause)` with
`comm_case ::= SendCase elem_type ch e | RecvCase elem_type ch`
(`lang.v:216,248,283-290`). The default case is inlined as the `option` so the
type system enforces at most one default (`new/golang/README.md:79-83`).

**[FACT]** Semantics (axioms of the `ChanSemantics` class,
`perennial:new/golang/defn/chan.v:95-114@43d4efab`): a `SelectStmt` step
nondeterministically picks **any permutation** of the non-default clauses
(`clauses' ≡ₚ clauses`) and reduces to `try_select`, which folds over the
permuted clauses calling the model's `TrySend`/`TryReceive` with
`blocking=true` iff there is no default (`defn/chan.v:40-62`). Non-blocking:
if no case fires, run the default. Blocking: if no case fires, reduce back to
`SelectStmt (SelectStmtClauses None clauses)` — i.e. retry forever
(`defn/chan.v:105-114`). Comment at `defn/chan.v:35-39`: "Shuffle the list of
non-default cases. Try the cases in order… if there's a default then select
it; else, go back to the beginning."

**[FACT]** Why new syntax at all: `perennial:new/golang/README.md:36-78` — a
design note ranking options (desugar > λ-encode > new syntax) and explaining
that select defeats λ-encoding because it needs a *variable-length list of
expressions evaluated to values* (would require list evaluation contexts). The
adopted split: the translator (goose.go:1780-1885) let-binds each channel
expression (`$ch_i`) and each send value (`$v_i`) *before* the `SelectStmt`
(fixing evaluation order per the Go spec), rewrites recv-case bindings
(`v := <-ch`, `v, ok := <-ch`) into a body lambda over `$recvVal`, and the
machine construct only ever sees values.

**[FACT]** Select support is complete in-kind at this rev: send cases, recv
cases (all binding forms), default, blocking and non-blocking. This is NEW —
Zhang's Feb-2025 thesis model explicitly lacked select ("the model does not
provide support for channel operations in select statements",
[MIT DSpace 1721.1/159079](https://dspace.mit.edu/handle/1721.1/159079)), and
goose's OLD (pre-`new`) translation had none of this machinery.

**[FACT]** The Go-side select model (`goose:model/channel/select.go`) —
`BlockingSelect2/3`, `NonBlockingSelect1/2/3` spinning on a
`primitive.RandomUint64()%n` coin — "is not used by Goose directly but only by
the tests (so the tests trust that this model matches the GooseLang model that
is actually used for verification)" (`select.go:3-5`). `RandomUint64` is
trusted-mapped to `ArbitraryInt` (demonic) (`primitive.v:33`).

### 2.3 The proof stack over the model

**[FACT]** Spec state (`perennial:new/golang/theory/chan/au_spec/
chan_au_base.v:8-28@43d4efab`):
`chanstate.t V ::= Buffered (buff : list V) | Idle | SndPending v | RcvPending
| SndCommit v | RcvCommit | Closed (drain : list V)` — a *logical* channel
state exposed to clients through `own_chan γ V s` (half of a ghost variable +
a capacity-validity fact, lines 83-103). `is_chan ch γ V` is the persistent
interface: the struct's `cap`/`mu` fields are frozen, and the mutex guards
`chan_inv_inner` = ∃ physical state, `chan_phys s ∗ chan_logical s`
(lines 434-454).

**[FACT]** Spec style: **HOCAP/logically-atomic updates via fancy-update
masks**, not TaDA-notation triples. E.g. blocking receive
(`chan_au_base.v:119-138`):

```
recv_au Φ := |={⊤,∅}=> ▷∃ s, own_chan s ∗ match s with
  | SndPending v      => own_chan RcvCommit ={∅,⊤}=∗ Φ v true
  | Idle              => own_chan RcvPending ={∅,⊤}=∗ recv_nested_au Φ
  | Closed []         => own_chan s ={∅,⊤}=∗ Φ (zero_val V) false
  | Closed (v::rest)  => own_chan (Closed rest) ={∅,⊤}=∗ Φ v true
  | Buffered (v::rest)=> own_chan (Buffered rest) ={∅,⊤}=∗ Φ v true
  | _ => True end
```

The unbuffered slow path is a **nested AU** (`recv_nested_au` /
`send_nested_au`): the client's update fires once to move `Idle→RcvPending`
and must then provide a *second* atomic update for the completion
(`SndCommit→Idle`). Top-level WPs: `wp_send/wp_receive/wp_close/wp_make2`
(`theory/chan.v:50-109`) take `is_chan` plus the AU (and a few later-credits
`£1`). The internal proof parks the client's AU *inside the lock invariant* as
saved propositions while an offer is outstanding (`chan_logical`,
`chan_au_base.v:385-432`; ghost `offer_lock`, `saved_offer`), which is how a
blocked sender's continuation is handed to the receiver that completes the
handshake. Proof bulk: `chan_au_send.v` 902 lines, `chan_au_recv.v` 829,
`chan_au_base.v` 691 — for a 293-line Go model.

**[FACT]** Select specs (`theory/chan.v@43d4efab`):

- `wp_select_blocking` (272-299): an **`∧`-conjunction** (`[∧ list]`) of
  per-case obligations — each case gets `is_chan` + its `send_au`/`recv_au`
  whose continuation is a WP of the case body. `∧` (not `∗`) because exactly
  one case fires.
- `wp_select_nonblocking` (427-455): same `∧` list of *nonblocking* AUs, plus
  `WP def` for the default.
- `wp_select_nonblocking_alt` (584-619): a **`∗`-separated** list where each
  case's not-ready branch yields a witness `Φnr`; if the default runs, ALL the
  witnesses are handed to it — enabling proofs that the default is
  *unreachable*. The docstring at `chan_au_base.v:244-263` candidly explains
  the two nonblocking-AU variants are incomparable and no canonical weakest
  spec is known.

**[FACT]** On top sit derived **idiom libraries**
(`theory/chan/idioms/@43d4efab`): `bag`, `broadcast` (close-as-broadcast,
renamed from "closeable"), `contrib`, `future`, `handshake`, `lock`
(channel-as-mutex), `mpmc` (1022 lines), `spsc` (668), and `dsp/` — **Actris
dependent separation protocols re-implemented over pairs of Go channels**
(`dsp.v:9-19`: "Protocol state is tracked using Actris iProto"; own
`proto_model.v`/`cofe_solver_2.v`). A `join.v` idiom existed and was deleted
2026-03-16 (perennial `7e66f5817`). Example programs verified against all
this: `goose:testdata/examples/channel/` — `fibonacci.go`, `muxer.go`,
`google_search.go`, `hedged.go`, `actris_example.go`,
`select_tricky_examples.go`, `parallel_search_replace`, `elimination_stack`,
`etcd_session`, `workq`, plus explicitly `*_unverified.go` files (cv,
leaky_buffer, muxer variant).

### 2.4 The recent-channel-work timeline (the thing the user flagged)

**[FACT]** From upstream history (clones; authors on `model/channel/`: Tej
Chajed 8, Levi Redlin 7):

| when | commit (repo) | what |
|---|---|---|
| 2024-08-13 | `a2c33b794` (perennial) | first `new/golang/defn/chan.v`: bare **axioms** for channel ops |
| Feb 2025 | — | Zhang MEng thesis: first real model + spec library, **no select** (old-goose lineage: `external/Goose/github_com/goose_lang/goose/channel.v`, 555 lines) |
| 2025-05-09 | `0fda1a6` (goose, PR #94) | channel model added to *new* goose |
| 2025-08-25 | `f4dd947` (goose, PR #121) | **fix select semantics** in model + simplifications |
| 2025-09-03 | `da51f4a` (goose, PR #130) | refactor to explicit offer states (current shape) |
| 2025-10-24..30 | `4f4d802`,`55541b5`,`5336bfa`,`10703eb`,`deb7917` (goose) | drop sync dep; readability; `Iter` model; adapt translation to new model; **tests keyed to Go spec statements** |
| 2025-11-04..07 | `c57f014`,`dba2b34` (goose) | select model split to own file; more tests |
| 2026-01-30 | `eb748d43e` (perennial) | old semantics deleted: old goose channel.v, `semantics.v` test corpus, **the GooseLang interpreter** |
| 2026-02-01..03-16 | perennial | theory push: `context` pkg translation (`31531af03`), select-recv translation fixes (`bed0145a6`), README + make-spec (`94a79322a`), **nested-select recv variable-capture bug fixed** (`8ace86ece`, 2026-03-12), thunking fix (`ec1e7d386`), `wp_select_nonblocking_alt` P-before-AU (`c7b2bc853`), idioms reorganized under `chan/` (`3bd133cc5`), future via saved_pred (`33a65c26b`) |
| 2026-03-12 | `19422b4` (goose, PR #187) | channel model README (the "empirically validating Go channel semantics" framing) |
| ~2026 | `aa59dcc` (goose) | goose README: "Development for this repository has moved to https://github.com/mit-pdos/perennial" |
| 2026-06-23 | `26deb7e5c` (perennial) | latest chan-theory touch (syntax modernization) |

**[FACT]** The consumer pulling this: `perennial:new/proof/go_etcd_io/raft/`
— an **in-progress verification of etcd-io/raft** (`v3_proof/protocol.v`
imports the `broadcast` and `bag` channel idioms and `chan_au_base`;
`readonly.v` is 955 lines; `new/code/go_etcd_io/{raft/v3, etcd/...}` are full
goose translations), plus `new/proof/go_etcd_io/etcd/client/v3/concurrency.v`
and `leasing.v`, and a translated `context` package. [ANALYSIS] Their channel
arc is being shaped by the same target as ours; their idiom set (broadcast/
done-channel, bag, future, spsc/mpmc) is effectively a map of which channel
patterns etcd/raft actually needs — useful directly for our corpus planning.

**[FACT]** No paper on the new channel model as of 2026-08-06 (searched; only
Zhang's thesis is indexed —
[Verification of Go Channels](https://dspace.mit.edu/handle/1721.1/159079)).

## 3. Goroutines and join

**[FACT]** Free fork only (§1.1). No join primitive; no goroutine identity.
Join is a *library/ghost* concern:

- `sync.WaitGroup`: the **real Go source** of `sync` is goose-translated
  (`perennial:new/code/sync.v:1` "autogenerated from sync") on top of a small
  trusted core (`perennial:new/trusted_code/sync.v@43d4efab`): `Mutex` impl
  replaced by `go.bool` + CmpXchg spinlock (lines 8-17), `runtime_Semacquire`
  replaced by an atomic-CAS spin model of the runtime semaphore (lines 30-58,
  with the runtime/sema.go source quoted), `runtime_Semrelease = AtomicAdd`
  (line 61), notifyList (Cond) **stubbed**: `Wait/NotifyAll/NotifyOne` are
  no-ops, `Add` returns `ArbitraryInt` (lines 19-28) — consistent with Cond
  being spin-semantics-only and "cv unverified" (goose `c20398a`). WaitGroup
  specs are proved over the translated real source, down to the bit-packed
  `counter‖waiter` word (`perennial:new/proof/sync_proof/waitgroup.v`, plus a
  `waitgroup_join.v` idiom).
- channels-as-join: the `handshake`/`broadcast`/`future` idioms (§2.3);
  the dedicated `join.v` idiom was deleted (2026-03-16, `7e66f5817`).

**[FACT]** Main-exit does NOT kill goroutines: the pool step never removes
threads (`language.v:118-122`), and adequacy is safety of every thread under
every interleaving. [ANALYSIS] Sound for their purposes: Go's real behavior
(program exits when main returns) only *removes* executions, so proving safety
of the superset is conservative; and since Perennial proves no liveness, the
extra "main finished but workers still stepping" executions cost nothing.
For GoLean the same question is livelier because our oracle *observes*
termination and output: `go run` of a program whose goroutines outlive main is
still deterministic in its observed output, so an interpreter that keeps
running orphan goroutines after main returns would diverge from the oracle in
side effects. We must model main-exit explicitly (stop scheduling at main
return), which is *more* faithful than Goose here.

**[FACT]** Blocking anywhere (channel ops, lock, Semacquire, blocking select)
is busy-waiting — spin loops in model code or self-reapplying `SelectStmt`.
There is no blocked/runnable distinction in the machine. [ANALYSIS] This is
free under partial-correctness WP (a spinning thread just never contributes),
but is a real cost for anyone wanting termination/fairness statements — and
would be painful for our differential runs (a deterministic scheduler
round-robining over spinners still works, but step counts explode; see §7).

## 4. Memory-model stance

**[FACT]** GooseLang is a sequentially consistent interleaving semantics with
races made UB by construction (§1.2 mechanism). The stated justification
(goose upstream `master:docs/implementation.md`, seen via clone; same text
summarized in the CoqPL'20 paper
[Verifying concurrent Go code in Coq with Goose](https://people.csail.mit.edu/nickolai/papers/chajed-goose-coqpl.pdf)):
"The translation takes into account Go's memory model. This memory model more
or less says races are not allowed, so the semantics of loads and stores
GooseLang makes racy access to the same pointer undefined behavior. This makes
it even more important to make struct fields independent pointers, so that it
isn't considered racy to simultaneously access different fields of the same
struct from multiple threads." I.e. the classic DRF-SC transfer: [the Go memory
model](https://go.dev/ref/mem) guarantees SC for data-race-free programs;
verified GooseLang programs cannot reach UB, hence are race-free, hence their
SC reasoning is sound on real hardware.

**[FACT]** Precise conflict matrix implied by `base_trans`
(`lang.v:1352-1431`): na-write conflicts with everything (needs `Reading 0`,
holds `Writing`); na-read conflicts with any write (atomic or not: `Load` is
fine under `Reading n` but `AtomicSwap`/`AtomicAdd`/successful `CmpXchg` need
`Reading 0`, and `PrepareWrite` needs `Reading 0`); na-read ∥ na-read and
atomic-anything ∥ atomic-anything are fine. So mixed atomic-write ∥ na-read is
UB — matching Go's memory model, which calls that a race.

**[FACT]** Honest caveat in their own README: "Many operations are carefully
modeled as being non-linearizable in Perennial, although this area is subtle
and hard to reconcile with Go's documented memory model"
(`goose:README.md:116@3be88bbb`).

[ANALYSIS] Comparison with GoLean's doctrine
(`docs/2026-08-04_nondeterminism-doctrine.md` lineage): identical stance —
DRF-SC, races fail closed. The difference is operational role: for them,
stuck-on-race is a *proof obligation generator* (nobody ever executes the
semantics); for us it must ALSO be an *executable classification* (interpreter
returns a race-UB outcome, fail-closed, never a value). Their naMode
instrumentation is the right concrete design for that and is fully
deterministic — it transfers verbatim. One extra asset we have that they
lack: `go run -race` gives us a (partial, dynamic) oracle for the race-UB
classification on corpus cases; Goose has no way to test its race semantics
at all.

## 5. Soundness / trust story

**[FACT]** Explicitly trusted: "The translator and semantics are trusted; you
can view the process as giving a semantics to Go"
(`goose:README.md:11@3be88bbb`). Their soundness framing (Goose paper /
GoJournal §Goose): the GooseLang model of a translated function should
*include all possible behaviors* of the Go original; then proofs transfer.

**[FACT]** Evidence mechanisms, past and present:

1. **(historical, now deleted)** The old semantics had an in-Rocq GooseLang
   interpreter plus a `semantics.v`/`unittest.v` corpus of translated Go test
   functions — Go tests that return `bool`, run natively via `go test` AND
   evaluated inside Rocq by the interpreter, checking both say `true`.
   Deleted with the old semantics 2026-01-30 (perennial `eb748d43e` removes
   `src/goose_lang/interpreter/*` and the corpora). **The new semantics
   currently has NO executable interpreter and no differential harness.**
2. **(current) the channel model is tested in Go**: `channel_test.go` ("tests
   adapted from the Go runtime channel test suite as well as additional
   tests", `goose:model/channel/README.md`), `channel_spec_test.go` ("Tests
   based on interpreting the text in the Go specification", lines 10-13, e.g.
   nil-channel blocking probed with timeouts), and `model/go_channel/` — the
   **same interface implemented over real Go channels** ("This is only used
   for testing the model - it makes it easy to use the same example with the
   model and Go channels", `go_channel/channel.go:1-4`), so examples like
   `muxer_test.go` run against both. This is genuine differential validation
   — but of the *Go model code*, in Go, not of the GooseLang semantics.
3. **Trusted, untested gaps**: the correspondence between `select.go`'s Go
   model and the GooseLang `try_select` axioms (`select.go:3-5` says the tests
   trust it); every `trusted_code/*.v` replacement (Mutex, sema, notifyList
   stubs, atomic package, primitive package); the translator itself; the
   `is_go_step` axiom classes (`ChanSemantics` etc.) — these are Rocq
   *axioms/typeclass assumptions*, discharged only by intended-model
   instantiation.

**[FACT]** Known divergences/gaps they document or embody: Cond unverified
(notifyList no-op stubs); runtime panics = stuck rather than catchable panics
(`recover` exists as a resolved builtin, `goose.go:853-856`, but e.g.
send-on-closed is UB, diverging from Go where it is *defined* behavior);
non-linearizability caveat (README:116); no liveness/fairness; goroutine leak
on main exit unmodeled (§3).

[ANALYSIS] Net: their trust chain for channels is
*Go spec text → Go model code (unit + differential-in-Go tests) → [trusted
goose translation] → Rocq definitions → verified AU specs*. The strongest
link (tested Go model) is exactly the piece we can consume directly; the
weakest links (translation, select axioms) are the pieces GoLean's
architecture already refuses to leave untested — our interpreter IS the
semantics and the differential gate runs it. We should also note their
regression: by deleting the old interpreter they *gave up* executable
validation of the semantics core; GoLean should not read that as "the field
says interpreters don't pay" — it was a casualty of the rewrite, and the
channel-model testing story (README framing: "empirically validating Go
channel semantics") shows they still want empirical grounding, now moved up a
level into Go itself.

## 6. The papers

**[FACT]** (verified titles/venues via search; model/proof summaries from the
papers' abstracts and the repos)

- **Perennial** — Chajed, Tassarotti, Kaashoek, Zeldovich, *Verifying
  concurrent, crash-safe systems with Perennial*, SOSP 2019. Iris-based
  program logic adding crash semantics (per-thread crash conditions, recovery
  reasoning) over GooseLang's thread-pool semantics; concurrency is plain
  Iris ghost state + invariants. Basis of everything later.
- **Goose** — Chajed, Kaashoek, Tassarotti, Zeldovich, *Verifying concurrent
  Go code in Coq with Goose*,
  [CoqPL 2020](https://people.csail.mit.edu/nickolai/papers/chajed-goose-coqpl.pdf).
  The translation approach: subset of Go, semantics-by-translation to
  GooseLang; races defined as unordered conflicting accesses and made UB by
  the two-step store trick (§1.2); structs exploded into independent field
  pointers; slices/maps/locks as libraries over primitives.
- **GoJournal** — Chajed, Tassarotti, Theng, Jung, Kaashoek, Zeldovich,
  [OSDI 2021](https://www.chajed.io/papers/gojournal:osdi2021.pdf). Largest
  old-goose verification: concurrent crash-safe journaling system (basis for
  DaisyNFS); exercised the lock/na-heap semantics heavily; specs in Perennial
  with logically-atomic crash-aware triples.
- **vMVCC** — Chang, Jung, Sharma, Tassarotti, Kaashoek, Zeldovich,
  [OSDI 2023](https://pdos.csail.mit.edu/papers/vmvcc:osdi23.pdf): verified
  MVCC transaction library in Go via Goose; prophecy variables (GooseLang's
  HeapLang-inherited `NewProph/ResolveProph`, `lang.v:244-245`) used at scale
  for future-dependent linearization points.
- **Grove** — Sharma, Jung, Tassarotti, Kaashoek, Zeldovich,
  [SOSP 2023](https://iris-project.org/pdfs/2023-sosp-grove.pdf): distributed
  separation logic over Goose'd Go (GroveKV): time-based leases, crash
  recovery, unreliable network as an FFI world; no channels (mutexes + RPCs).
- **Zhang thesis** — *Verification of Go Channels*, MIT MEng, Feb 2025
  ([DSpace](https://dspace.mit.edu/handle/1721.1/159079)), advisor Zeldovich.
  First channel support: GooseLang channel model, translator extension, spec
  library for open channels; **no select**; superseded by the Redlin/Chajed
  model within the year.
- **The current channel model: no paper yet** (searched 2026-08-06; the
  in-tree artifacts — model README, `new/golang/README.md` design note, the
  etcd/raft proofs — are the primary sources). Development of goose has moved
  into mit-pdos/perennial (`goose:README.md:3-4`).

## 7. Copy vs diverge for GoLean

Constraints recap (ours): executable deterministic-given-stream interpreter is
the semantics AND the statement language; differential validation against
`go run`; kernel reducibility; statements in interpreter-level pre/post terms;
Iris internal-only.

**(a) Channels as library-over-locks vs machine primitive — DIVERGE (at the
machine), COPY (the state machine and its Go source).**
[ANALYSIS] Their library choice is motivated by proof economics: no new
language rules to trust beyond `SelectStmt`, specs proven once against
translated code, and the model is testable in Go. The costs they pay:
spin-loop blocking, a 2400-line AU/ghost proof stack to recover what a
primitive would give directly, and a trusted select-axioms↔model gap. For
GoLean the executability requirement flips the calculus: a channel as an
interpreter primitive with explicit state — literally their `chanstate.t`
(`Buffered buff | Idle | SndPending v | RcvPending | SndCommit v | RcvCommit |
Closed drain`, plus cap) — gives us (i) O(1) deterministic steps instead of
offer-protocol spinning, (ii) a first-order channel state that can appear in
theorem statements (their `chanstate.t` is exactly statement-shaped; their
`own_chan`/AUs are not, and our doctrine forbids the Iris layer in statements
anyway), (iii) blocked-thread bookkeeping so the scheduler can skip
non-runnable threads. Their *Go model code* is still gold for us — as corpus
input: `model/channel/channel.go` + `channel_spec_test.go` + the
`testdata/examples/channel/*` programs are canonical Go we can run under
`go run` AND under our interpreter once channels land; their spec-text tests
map one-to-one onto guardrail cases (nil ops, drain-after-close, close-during-
handshake, len/cap, for-range, unbuffered rendezvous, nonblocking-select
asymmetry).

**(b) Their select design — COPY the decomposition, adapt the choice point.**
[ANALYSIS] Two pieces transfer cleanly: (1) the *translation-side* evaluation
discipline (channel exprs and send values evaluated to values, in order,
before the select; recv bindings desugared into the case body) — this is
frontend work in `NativeToIR`, and their README:36-78 is the argument for why
you do NOT want variable-arity expression evaluation inside the construct;
(2) the *semantic envelope*: any ready case may be chosen; with a default,
readiness is tested once (with the crucial no-offer asymmetry for unbuffered
channels) and default taken if none ready. For us the permutation
nondeterminism becomes ONE choice-stream consumption (index into the ready
set — or a permutation if we want to expose their exact envelope); Go spec
text ("uniform pseudo-random" choice among ready cases) pins the envelope,
and per our nondeterminism doctrine the too-wide direction (their retry-loop
allows starving a perpetually-ready case — possibilistically fine, no
`go run` counterexample possible) must be argued against spec text, not
tests. Their blocking-select-as-retry should become block-on-wait-set for us
(same reason as (a)).

**(c) Fork/thread pool — COPY almost verbatim.** [ANALYSIS] `Fork` appending
to a thread list, one interleaving choice per step, args evaluated in the
caller: all deterministic-given-stream compatible (stream picks the thread
index). Two divergences: we must add main-exit-terminates (observable in the
oracle, §3) and a runnable/blocked partition (else deterministic replay of
spin loops is livelock-prone and fuel-explosive). Their "no fairness, no
liveness" stance we inherit for now — but note our differential runs need a
*complete* schedule to compare outputs, so the default stream should encode a
scheduler that always finds progress when progress exists (their semantics
never needed one).

**(d) naMode race instrumentation — COPY.** [ANALYSIS] The
`Reading n | Writing` cell-mode design (§1.2) is executable, deterministic,
and makes DRF-SC-races-fail-closed an operational outcome (interpreter
reports race-UB; classification per our fail-closed rules, never a value; not
counted as pass). Their two-step na accesses are the honest granularity — and
directly answer our BUG-002 class by making sub-step interleavings explicit
in the machine rather than discovered later. Cost we accept consciously:
per-field struct decomposition (their "struct fields as independent
pointers") interacts with our value model — needs its own design slice; the
granularity ledger should record every load/store decomposition decision with
the Go-memory-model argument, since no test can check it (their lesson and
ours coincide).

**(e) sync layering — COPY the shape.** [ANALYSIS] Tiny trusted core
(Mutex-as-flag + CAS; semaphore counter) + real translated source above it is
exactly the right split for us too: GoLean can make Mutex/sema interpreter
primitives with differential guardrails (`sync` corpus cases run under
`go run`), and gets WaitGroup/RWMutex/Once behavior from Go source if/when
frontend coverage reaches it — with their `trusted_code/sync.v` as the list
of exactly which runtime hooks need primitive treatment. Their Cond stubs are
a warning: notifyList semantics is where they punted; we should keep Cond
fail-closed until we can pin it with corpus cases.

**(f) Panics — DIVERGE.** [ANALYSIS] They collapse runtime panics into UB
(stuck), making send-on-closed a proof obligation. Go defines these as panics
(catchable, observable exit code/message) and our oracle observes them;
GoLean already models panic values (PanicNilError work). We should model
send-on-closed / double-close / close-of-nil as real Go panics — strictly
more faithful, differential-testable, and it keeps "verified ⇒ no panic"
as a spec-level choice rather than a semantics-level one.

**(g) Statement TCB.** [ANALYSIS] Their client-facing channel reasoning is
irreducibly higher-order Iris (AUs with nested masks, saved-prop offer
parking). None of that can be our statement idiom — but it doesn't need to
be: the lesson to import is that `chanstate.t` (first-order) is the interface
between machine and specs, and all the Iris machinery lives strictly above
it. Our headline channel theorems should be stated over interpreter channel
states; if we later build an Iris-internal law layer, their AU catalog
(blocking/nonblocking/alt, the documented incomparability at
`chan_au_base.v:244-263`, the `∧`-vs-`∗` select-spec distinction and the
default-unreachable pattern) is the best existing map of what channel laws
clients actually need — each one we adopt needs a discharge witness per our
non-vacuity gate.

**(h) Their target overlap.** [ANALYSIS] `new/proof/go_etcd_io/raft` +
`context` + etcd client proofs mean Perennial is actively walking toward the
same north star. Worth tracking upstream (their idiom needs = raft's channel
patterns) and worth an explicit design-note comparison when our channels arc
starts, per the CLAUDE.md deps-comparison practice.

---

### Loose ends / could not verify

- The exact Zhang-thesis spec style (her AU formulation vs the current one) —
  thesis PDF not read in full; cited only for scope (no select) and dates.
- Perennial's Rocq-side proof-completeness for every model path (e.g. whether
  `Len`/`Cap`/`Iter` have finished WPs) — not audited; `a021c6fee` ("Resolve
  admit in wp_NewChannel", 2026-03-16) shows admits existed transiently.
- Whether any GooseLang-executable testing replacement is planned post-rewrite
  — nothing found in-tree or in issues (not searched exhaustively).
