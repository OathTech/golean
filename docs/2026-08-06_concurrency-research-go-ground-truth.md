# Go concurrency ground truth — channels, goroutines, select (2026-08-06)

Status: RESEARCH DRAFT for the channels/goroutines arc. Not doctrine; raw
material for the arc's design note and envelope statements.
Points are tagged **[FACT]** (verified against a primary source, cited
verbatim) or **[ANALYSIS]** (our reasoning on top of the facts).
Binding doctrine this feeds: `docs/2026-08-04_nondeterminism-doctrine.md`
(envelope statements, ∀-stream theorems), CLAUDE.md (fail-closed,
guardrails first).

Sources and toolchain at time of writing:
- Spec: `/usr/local/go/doc/go_spec.html` (the go1.26.5 spec; line numbers cited).
- Memory model: `/usr/local/go/doc/go_mem.html` (ships with go1.26.5; this IS
  the post-2022-revision text of https://go.dev/ref/mem — it contains the
  Boehm–Adve formalization and the sync/atomic SC rule added in the revision).
- Runtime: `/usr/local/go/src/runtime/chan.go`, `select.go`, `proc.go`.
- Rationale: Russ Cox, research.swtch.com/mm (series index) and
  research.swtch.com/gomm ("Updating the Go Memory Model", 2021 — the
  proposal the 2022 revision implemented). Fetched 2026-08-06.
- Oracle: go1.26.5 linux/amd64 (`go version go1.26.5 linux/amd64`). All probe
  outputs below are verbatim from this toolchain. Probe sources:
  `.tmp/conc-probes/p01…p26*.go` (+ `run*.sh`).

---

## 1. Spec text — every rule, every latitude

### 1.1 Channel types (`go_spec.html:1685-1767`)

**[FACT]** Purpose and nil (`go_spec.html:1687-1695`):
> "A channel provides a mechanism for concurrently executing functions to
> communicate by sending and receiving values of a specified element type.
> The value of an uninitialized channel is `nil`."

**[FACT]** Directionality (`go_spec.html:1701-1708`): `chan T`, `chan<- T`,
`<-chan T`; "A channel may be constrained only to send or only to receive by
assignment or explicit conversion." (Direction is a static type property —
compile-time only; no dynamic direction state.)

**[FACT]** make + capacity (`go_spec.html:1727-1745`):
> "The capacity, in number of elements, sets the size of the buffer in the
> channel. If the capacity is zero or absent, the channel is unbuffered and
> communication succeeds only when both a sender and receiver are ready.
> Otherwise, the channel is buffered and communication succeeds without
> blocking if the buffer is not full (sends) or not empty (receives).
> A `nil` channel is never ready for communication."

**[FACT]** FIFO is SPEC, not implementation latitude (`go_spec.html:1757-1767`):
> "A single channel may be used in send statements, receive operations, and
> calls to the built-in functions `cap` and `len` by any number of goroutines
> without further synchronization. Channels act as first-in-first-out queues.
> For example, if one goroutine sends values on a channel and a second
> goroutine receives them, the values are received in the order sent."

**[ANALYSIS]** Two load-bearing readings of that paragraph: (a) len/cap/send/
recv/close on a shared channel are never a data race — the channel itself is
a synchronization object; (b) the FIFO guarantee is stated for the
one-sender/one-receiver observation ("one goroutine sends … a second
receives"). With MULTIPLE senders or receivers, the per-channel value queue
is still FIFO at the buffer level (spec sentence one: "Channels act as
first-in-first-out queues"), but which goroutine's send enqueues first is
scheduling latitude, so cross-goroutine arrival order is NOT pinned by this
text. The waiter-wakeup order (which of several blocked receivers gets the
next value) is not addressed by the spec AT ALL — see §6 row L4.

**[FACT]** Reference semantics (`go_spec.html:1806`): "A map or channel value
is a reference to the implementation-specific data structure holding the
elements" (from §Representation of values; the word "implementation-specific"
here is about the data structure, not observable behavior).

### 1.2 Go statements (`go_spec.html:6910-6944`)

**[FACT]** (`go_spec.html:6912-6916`):
> "A 'go' statement starts the execution of a function call as an independent
> concurrent thread of control, or goroutine, within the same address space."

**[FACT]** Evaluation and detachment (`go_spec.html:6928-6938`):
> "The function value and parameters are evaluated as usual in the calling
> goroutine, but unlike with a regular call, program execution does not wait
> for the invoked function to complete. Instead, the function begins executing
> independently in a new goroutine. When the function terminates, its
> goroutine also terminates. If the function has any return values, they are
> discarded when the function completes."

**[FACT]** The expression must be a function or method call and "it cannot be
parenthesized. Calls of built-in functions are restricted as for expression
statements" (`go_spec.html:6923-6925`).

**[FACT — absence]** The spec says NOTHING about scheduling: no fairness, no
preemption, no ordering between runnable goroutines, no goroutine identity
values. Searched the whole spec for "fair", "schedul", "preempt" — the only
scheduling-adjacent sentences are the Select pseudo-random rule
(`go_spec.html:6995`) and Program execution's main-exit rule
(`go_spec.html:8391`). **[ANALYSIS]** Goroutine scheduling order is therefore
pure latitude bounded only by the memory model (§2): any interleaving
consistent with happens-before is a legal execution. There is no spec
guarantee that a runnable goroutine ever runs (starvation is legal per spec
text), though DRF-SC plus blocking-op semantics constrain what a schedule can
observe. This is the widest latitude point in the whole surface (§6 row L1).

### 1.3 Send statements (`go_spec.html:6062-6096`)

**[FACT]** The complete send rule (`go_spec.html:6077-6084`):
> "Both the channel and the value expression are evaluated before
> communication begins. Communication blocks until the send can proceed.
> A send on an unbuffered channel can proceed if a receiver is ready.
> A send on a buffered channel can proceed if there is room in the buffer.
> A send on a closed channel proceeds by causing a run-time panic.
> A send on a `nil` channel blocks forever."

Static rules (`go_spec.html:6064-6069`): channel expression must be of
channel type, direction must permit send, value assignable to element type.

### 1.4 Receive operator (`go_spec.html:5303-5347`)

**[FACT]** The complete receive rule (`go_spec.html:5305-5316`):
> "For an operand `ch` of channel type, the value of the receive operation
> `<-ch` is the value received from the channel `ch`. The channel direction
> must permit receive operations, and the type of the receive operation is
> the element type of the channel. The expression blocks until a value is
> available. Receiving from a `nil` channel blocks forever. A receive
> operation on a closed channel can always proceed immediately, yielding the
> element type's zero value after any previously sent values have been
> received."

**[FACT]** comma-ok (`go_spec.html:5332-5347`): the forms `x, ok = <-ch`,
`x, ok := <-ch`, `var x, ok = <-ch`, `var x, ok T = <-ch`
> "yields an additional untyped boolean result reporting whether the
> communication succeeded. The value of `ok` is `true` if the value received
> was delivered by a successful send operation to the channel, or `false` if
> it is a zero value generated because the channel is closed and empty."

### 1.5 Select statements (`go_spec.html:6947-7069`)

**[FACT]** The five execution steps, verbatim (`go_spec.html:6981-7017`):
> "1. For all the cases in the statement, the channel operands of receive
> operations and the channel and right-hand-side expressions of send
> statements are evaluated exactly once, in source order, upon entering the
> 'select' statement. The result is a set of channels to receive from or send
> to, and the corresponding values to send. Any side effects in that
> evaluation will occur irrespective of which (if any) communication operation
> is selected to proceed. Expressions on the left-hand side of a RecvStmt with
> a short variable declaration or assignment are not yet evaluated.
> 2. If one or more of the communications can proceed, a single one that can
> proceed is chosen via a uniform pseudo-random selection. Otherwise, if there
> is a default case, that case is chosen. If there is no default case, the
> 'select' statement blocks until at least one of the communications can
> proceed.
> 3. Unless the selected case is the default case, the respective
> communication operation is executed.
> 4. If the selected case is a RecvStmt with a short variable declaration or
> an assignment, the left-hand side expressions are evaluated and the received
> value (or values) are assigned.
> 5. The statement list of the selected case is executed."

**[FACT]** nil channels in select (`go_spec.html:7020-7022`):
> "Since communication on `nil` channels can never proceed, a select with
> only `nil` channels and no default case blocks forever."

**[FACT]** `select {}` blocks forever (example at `go_spec.html:7066`:
"`select {}  // block forever`").

Grammar (`go_spec.html:6960-6966`): at most one default case, may appear
anywhere in the case list. RecvStmt may assign to one or two variables.

**[ANALYSIS]** "uniform pseudo-random selection" (`go_spec.html:6995`) is the
doctrine's canonical select-latitude example, and its exact strength matters:
the spec pins UNIFORMITY over the ready set (a distributional claim!) but
"pseudo-random" leaves the distribution's realization unpinned. A
possibilistic envelope (any ready case may be chosen, every ready case is
choosable) is strictly weaker than the spec text — it drops the uniformity.
For ∀-stream theorems that is the sound direction (our envelope ⊇ any
uniform sampler's support, and no theorem can rely on distribution). But note
the asymmetry: a Go program CAN legitimately rely on uniformity for
probabilistic termination/fairness (e.g. the spec's own random-bit-generator
example at `go_spec.html:7055-7060`); under a pure possibilistic envelope
such programs have infinite adversarial executions. Any liveness-flavored
claim is out of scope unless we add fairness assumptions — record that
explicitly in the arc design note.

**[ANALYSIS]** Step 1 fixes an evaluation-order rule that our interpreter must
implement exactly: channel operands AND send RHS values are evaluated once, in
source order, before any choice; recv LHS only after selection. A select that
panics during step-1 evaluation panics regardless of case readiness.

### 1.6 Close (`go_spec.html:7496-7509`)

**[FACT]** The complete close rule (`go_spec.html:7498-7509`):
> "For a channel `ch`, the built-in function `close(ch)` records that no more
> values will be sent on the channel. It is an error if `ch` is a receive-only
> channel. Sending to or closing a closed channel causes a run-time panic.
> Closing the nil channel also causes a run-time panic. After calling `close`,
> and after any previously sent values have been received, receive operations
> will return the zero value for the channel's type without blocking. The
> multi-valued receive operation returns a received value along with an
> indication of whether the channel is closed."

### 1.7 make(chan, n) (`go_spec.html:7682-7736`)

**[FACT]** `make(T)` → "unbuffered channel of type T"; `make(T, n)` →
"buffered channel of type T, buffer size n" (`go_spec.html:7700-7702`).

**[FACT]** Size argument rule (`go_spec.html:7717-7726`): size must be of
integer type / untyped constant; "A constant size argument must be
non-negative and representable by a value of type `int`"; "For slices and
channels, if n is negative or larger than m at run time, a run-time panic
occurs." (For channels there is no `m`; the operative clause is `n` negative
⇒ run-time panic. Probe p21 §4.13 shows the panic value.)

### 1.8 len/cap on channels (`go_spec.html:7611-7659`)

**[FACT]** (`go_spec.html:7620-7632`): `len(chan T)` = "number of elements
queued in channel buffer"; `cap(chan T)` = "channel buffer capacity".
"The implementation guarantees that the result always fits into an `int`."

**[FACT]** (`go_spec.html:7654-7657`):
> "The length of a `nil` slice, map or channel is 0.
> The capacity of a `nil` slice or channel is 0."

**[ANALYSIS]** len/cap on channels are always non-constant and never panic
(no nil-channel exception, unlike send/recv/close). Under concurrency, len
is a momentary snapshot with no stability guarantee — the spec's "without
further synchronization" sentence (§1.1) makes it race-free but says nothing
about which moment is observed (§6 row L7).

### 1.9 Channel comparison (`go_spec.html:5156-5159`)

**[FACT]** verbatim:
> "Channel types are comparable. Two channel values are equal if they were
> created by the same call to `make` or if both have value `nil`."

**[ANALYSIS]** Reference identity — channels are valid map keys with identity
semantics (probe p12, §4.11). Note `==` on channels never compares direction
or element snapshots; a directional conversion of the same channel remains
equal (same `make` call) but the comparison must be well-typed.

### 1.10 Program execution and init (`go_spec.html:8373-8391`, `8355-8371`)

**[FACT]** main-exit rule (`go_spec.html:8387-8391`):
> "Program execution begins by initializing the program and then invoking the
> function `main` in package `main`. When that function invocation returns,
> the program exits. It does not wait for other (non-`main`) goroutines to
> complete."

**[FACT]** init concurrency (`go_spec.html:8362-8371`):
> "Package initialization—variable initialization and the invocation of
> `init` functions—happens in a single goroutine, sequentially, one package
> at a time. An `init` function may launch other goroutines, which can run
> concurrently with the initialization code. However, initialization always
> sequences the `init` functions: it will not invoke the next one until the
> previous one has returned."

**[FACT]** Run-time panics carry "a value of the implementation-defined
interface type `runtime.Error`"; "The exact error values that represent
distinct run-time error conditions are unspecified" (`go_spec.html:8420-8426`).
**[ANALYSIS]** So the STRINGS "send on closed channel" etc. (§4) are
implementation detail; the spec pins only THAT a run-time panic occurs.
Matches how the repo already treats other runtime panic values.

### 1.11 Full latitude-keyword sweep of the spec

**[FACT]** `grep -n -iE 'unspecified|implementation-|pseudo-random|not specified'`
over the whole spec returns 24 hits; the concurrency-surface ones are:
`6995` (select "uniform pseudo-random"), `1806` (channel value is a reference
to "the implementation-specific data structure"), `8422`/`8426` (runtime.Error
type and values), `8291`/`8314` (package-level initialization order details),
`7740` (map size hint, not channels). Everything else (floats, print,
evaluation order at `5864-5874`, map iteration `6750`) is outside this arc.
There is NO "unspecified" keyword on scheduling, waiter order, or deadlock —
those latitudes exist by OMISSION, not by marked text. **[ANALYSIS]** For the
envelope inventory this distinction matters: marked latitudes have bounding
text to argue against; omission latitudes (§6 rows L1, L4, L8) are bounded
only by the memory model and by "communication blocks until it can proceed".

---

## 2. The memory model (`/usr/local/go/doc/go_mem.html`, current revision)

### 2.1 The frame

**[FACT]** Scope (`go_mem.html:15-18`): "The Go memory model specifies the
conditions under which reads of a variable in one goroutine can be guaranteed
to observe values produced by writes to the same variable in a different
goroutine."

**[FACT]** Data race definition + DRF-SC (`go_mem.html:46-58`):
> "A data race is defined as a write to a memory location happening
> concurrently with another read or write to that same location, unless all
> the accesses involved are atomic data accesses as provided by the
> `sync/atomic` package. … In the absence of data races, Go programs behave
> as if all the goroutines were multiplexed onto a single processor. This
> property is sometimes referred to as DRF-SC: data-race-free programs
> execute in a sequentially consistent manner."

**[FACT]** The racy-program calibration paragraph (`go_mem.html:60-74`) —
quote in full, this is the fail-closed anchor:
> "While programmers should write Go programs without data races, there are
> limitations to what a Go implementation can do in response to a data race.
> An implementation may always react to a data race by reporting the race and
> terminating the program. Otherwise, each read of a single-word-sized or
> sub-word-sized memory location must observe a value actually written to
> that location (perhaps by a concurrent executing goroutine) and not yet
> overwritten. These implementation constraints make Go more like Java or
> JavaScript, in that most races have a limited number of outcomes, and less
> like C and C++, where the meaning of any program with a race is entirely
> undefined, and the compiler may do anything at all. Go's approach aims to
> make errant programs more reliable and easier to debug, while still
> insisting that races are errors and that tools can diagnose and report
> them."

**[FACT]** Formal definitions (`go_mem.html:80-215`): follows Boehm–Adve
(PLDI 2008). Memory operations are read-like (read, atomic read, mutex lock,
channel receive) or write-like (write, atomic write, mutex unlock, channel
send, channel close) (`go_mem.html:108-110`). Requirement 1: per-goroutine
sequential correctness consistent with "sequenced before" = the spec's
control-flow + evaluation order (`go_mem.html:117-125`). Requirement 2: W
restricted to synchronizing ops is explainable by an implicit TOTAL order
consistent with sequencing and values (`go_mem.html:133-138`).
"happens before" = transitive closure of (sequenced before ∪ synchronized
before) (`go_mem.html:153-156`). Requirement 3 (visibility, `go_mem.html:158-167`):
a non-synchronizing read r of x must read a write w with (1) w happens before
r, (2) no intervening w' with w hb w' hb r. Data races = hb-unordered
read/write or write/write pairs, at least one non-synchronizing
(`go_mem.html:169-184`). DRF ⇒ SC stated at `go_mem.html:193-200`.

### 2.2 Implementation restrictions for racy programs (`go_mem.html:216-282`)

**[FACT]** (`go_mem.html:224-229`): "Any implementation can, upon detecting a
data race, report the race and halt execution of the program. Implementations
using ThreadSanitizer (accessed with 'go build -race') do exactly this."

**[FACT]** Word-tearing latitude (`go_mem.html:231-239`): reads/writes of
arrays, structs, complex numbers "may be implemented as a read of each
individual sub-value … in any order."

**[FACT]** Word-sized reads (`go_mem.html:241-249`): a read of a location "not
larger than a machine word must observe some write w such that r does not
happen before w and there is no write w' such that w happens before w' and w'
happens before r. That is, each read must observe a value written by a
preceding or concurrent write." Plus (`go_mem.html:251-253`): "observation of
acausal and 'out of thin air' writes is disallowed."

**[FACT]** Multiword corruption — the "may also crash" substance
(`go_mem.html:255-273`):
> "Reads of memory locations larger than a single machine word are encouraged
> but not required to meet the same semantics … implementations may instead
> treat larger operations as a set of individual machine-word-sized operations
> in an unspecified order. This means that races on multiword data structures
> can lead to inconsistent values not corresponding to a single write. When
> the values depend on the consistency of internal (pointer, length) or
> (pointer, type) pairs, as can be the case for interface values, maps,
> slices, and strings in most Go implementations, such races can in turn lead
> to arbitrary memory corruption."

**[ANALYSIS]** Calibration for our races-fail-closed stance: racy Go is NOT
C-style UB, but the guarantee floor is (a) word-sized reads see some
previously/concurrently written value, (b) no out-of-thin-air — and the
ceiling includes "report and terminate" and, through multiword races,
"arbitrary memory corruption". There is no usable envelope for a verifier
below the DRF line: modeling racy outcomes faithfully would mean modeling
torn multiword values and corruption. Refusing to assign semantics to racy
programs (fail closed) is strictly sound — every guarantee we would forgo is
one the model above cannot state without a memory-layout model. This matches
the doctrine's membership-lane framing: DRF programs get SC interleaving
semantics (our `Choices` stream ranges over SC interleavings + select picks +
waiter picks); racy programs get `.unsupported`/no-theorem.

### 2.3 Channel happens-before rules (`go_mem.html:363-489`)

The four rules, verbatim (each marked `class="rule"` in the source):

**[FACT]** Send→recv (`go_mem.html:372-375`):
> "A send on a channel is synchronized before the completion of the
> corresponding receive from that channel."

**[FACT]** Close→recv-zero (`go_mem.html:404-407`):
> "The closing of a channel is synchronized before a receive that returns a
> zero value because the channel is closed."

**[FACT]** Unbuffered recv→send-completion (`go_mem.html:413-416`):
> "A receive from an unbuffered channel is synchronized before the completion
> of the corresponding send on that channel."
With the explicit caveat (`go_mem.html:446-451`): "If the channel were
buffered (e.g., c = make(chan int, 1)) then the program would not be
guaranteed to print 'hello, world'. (It might print the empty string, crash,
or do something else.)"

**[FACT]** Buffered generalization (`go_mem.html:453-455`):
> "The kth receive from a channel with capacity C is synchronized before the
> completion of the k+Cth send on that channel."
(`go_mem.html:457-464`: this is what makes a buffered channel a counting
semaphore.)

**[ANALYSIS]** Note the direction asymmetry: send-synchronized-before-receive
holds for ALL channels; receive-synchronized-before-send-completion holds for
unbuffered channels (generalized to the k/k+C rule for buffered). A model
that executes channel ops atomically at a rendezvous/commit point under an SC
interleaving semantics automatically satisfies all four rules — the rules
only have independent bite for weaker-than-SC implementations. Since our
interpreter IS an SC interleaving machine, the memory model imposes no extra
obligation on it; the obligation is on the DRF precondition (§2.2).

### 2.4 Goroutine creation/destruction (`go_mem.html:304-361`)

**[FACT]** (`go_mem.html:306-309`): "The go statement that starts a new
goroutine is synchronized before the start of the goroutine's execution."

**[FACT]** (`go_mem.html:335-338`): "The exit of a goroutine is not guaranteed
to be synchronized before any event in the program." And (`go_mem.html:352-355`):
"In fact, an aggressive compiler might delete the entire go statement" (for a
goroutine whose effects are unobserved).

**[FACT]** Init (`go_mem.html:288-302`): "Program initialization runs in a
single goroutine, but that goroutine may create other goroutines, which run
concurrently." Rules: q's init completion synchronized-before importer p's
init start; "The completion of all init functions is synchronized before the
start of the function main.main."

### 2.5 sync / atomic (record; likely out of arc scope)

**[FACT]** Mutex (`go_mem.html:495-500`): "For any sync.Mutex or sync.RWMutex
variable l and n < m, call n of l.Unlock() is synchronized before call m of
l.Lock() returns." RWMutex and TryLock rules at `go_mem.html:530-546`
(notably: "l.TryLock … may be considered to be able to return false even when
the mutex l is unlocked" — an explicit spurious-failure latitude).

**[FACT]** Once (`go_mem.html:556-559`): "The completion of a single call of
f() from once.Do(f) is synchronized before the return of any call of
once.Do(f)."

**[FACT]** Atomics (`go_mem.html:597-607`): "If the effect of an atomic
operation A is observed by atomic operation B, then A is synchronized before
B. All the atomic operations executed in a program behave as though executed
in some sequentially consistent order." — "the same semantics as C++'s
sequentially consistent atomics and Java's volatile variables."

**[FACT]** WaitGroup's rule lives in package docs, not go_mem
(`/usr/local/go/src/sync/waitgroup.go:151-152`): "a call to Done
'synchronizes before' the return of any Wait call that it unblocks."

### 2.6 Rationale (Russ Cox, research.swtch.com/mm + /gomm)

**[FACT]** The series: "Hardware Memory Models" (research.swtch.com/hwmm),
"Programming Language Memory Models" (research.swtch.com/plmm), "Updating the
Go Memory Model" (research.swtch.com/gomm) (index fetched 2026-08-06).

**[FACT]** From gomm (fetched 2026-08-06): "Go's approach sits between these
two. Programs with data races are invalid in the sense that an implementation
may report the race and terminate the program. But otherwise, programs with
data races have defined semantics with a limited number of outcomes, making
errant programs more reliable and easier to debug." And: "Go does not take
this approach: there is no 'undefined behavior.' In particular, bugs like
null pointer dereferences, integer overflow, and unintentional infinite loops
all have defined semantics in Go."

**[ANALYSIS]** Load-bearing for us only as confirmation that the 2022 text's
limited-outcomes stance is deliberate design (fault isolation/debuggability),
i.e. we should not expect it to widen toward C-style UB in future revisions.

---

## 3. Runtime behavior (go1.26.5 `runtime/chan.go`, `select.go`, `proc.go`)

All of §3 is implementation, cited to pin WHICH behaviors the flagship
implementation realizes inside the spec envelope — not to promote them to
spec. Language-level observability noted per item.

### 3.1 hchan and the two queues

**[FACT]** `chan.go:34-55`: `hchan` = circular buffer (`buf`, `dataqsiz`,
`qcount`, `sendx`, `recvx`), `closed` flag, and two waiter queues `recvq`,
`sendq` of `sudog`s, all under one `lock`. Invariant comment `chan.go:9-18`:
"At least one of c.sendq and c.recvq is empty" (except a single goroutine
select-blocking on both sides of one unbuffered channel).

**[FACT]** Waiter queues are FIFO: `waitq.enqueue` appends at tail
(`chan.go:872-884`), `waitq.dequeue` pops from head (`chan.go:886-919`),
with one wrinkle — a dequeued select-waiter is skipped if another case
already won its select (`sgp.isSelect && !CompareAndSwap(selectDone)`,
`chan.go:911-916`).

### 3.2 Send path (`chansend`, `chan.go:176-310`)

**[FACT]** In order:
1. nil channel → `gopark(…waitReasonChanSendNilChan, traceBlockForever…)`
   — parks forever (`chan.go:177-183`).
2. closed → `panic(plainError("send on closed channel"))` (`chan.go:224-227`).
3. waiting receiver → DIRECT HANDOFF: "Found a waiting receiver. We pass the
   value we want to send directly to the receiver, bypassing the channel
   buffer (if any)" (`chan.go:229-233`, `send()` at 318-351 →
   `sendDirect` write into the receiver's stack slot, `chan.go:392-403`).
4. buffer room → enqueue at `sendx`, advance circularly (`chan.go:237-252`).
5. else park on `sendq`; on wakeup, if woken by close → panic
   "send on closed channel" (`chan.go:303-308`).

**[ANALYSIS]** Direct handoff means a send to a BUFFERED channel with a
waiting receiver skips the buffer entirely (legal only because a waiting
receiver implies empty buffer, per the hchan invariant — FIFO is preserved).
Language-level, handoff vs buffer transit is unobservable EXCEPT through
`len(ch)` snapshots: a third goroutine polling len never sees the handed-off
element occupy the buffer. Since len-under-concurrency is already snapshot
latitude (§6 row L7), an interpreter that models rendezvous as
enqueue+immediate-dequeue at one atomic step is observationally equivalent.

### 3.3 Receive path (`chanrecv`, `chan.go:524-700`; `recv`, 702-746)

**[FACT]** In order: nil → park forever (`chan.go:532-538`); closed AND
empty → return zero value, `(selected=true, received=false)`
(`chan.go:588-599` slow path, `548-578` lock-free fast path); waiting
sender → `recv()`: if unbuffered, `recvDirect` from sender's stack; if
buffered (necessarily full), "Take the item at the head of the queue. Make
the sender enqueue its item at the tail of the queue. Since the queue is
full, those are both the same slot" (`chan.go:707-736`) — FIFO preserved
through the blocked-sender window; else buffer → dequeue head
(`chan.go:631-646`); else park on `recvq`.

**[FACT]** A channel closed WITH data still in the buffer drains in FIFO
order with `ok=true` before yielding zeros with `ok=false`: `chan.go:588-601`
("The channel has been closed, but the channel's buffer have data.").
Probe p06 (§4.5) confirms observably.

### 3.4 Close path (`closechan`, `chan.go:414-487`)

**[FACT]** nil → panic "close of nil channel" (`chan.go:415-417`); already
closed → panic "close of closed channel" (`chan.go:423-426`); then sets
`closed=1`, dequeues ALL blocked receivers (each gets zero value,
`sg.success=false`) and ALL blocked senders ("release all writers (they will
panic)", `chan.go:460-476`), and readies them after dropping the lock.
Probe p24 (§4.15) shows the woken sender's panic is recoverable in that
goroutine.

### 3.5 Select (`selectgo`, `select.go:107-459`)

**[FACT]** Poll order is a uniform Fisher–Yates shuffle: for each case with a
non-nil channel, `j := cheaprandn(uint32(norder + 1)); pollorder[norder] =
pollorder[j]; pollorder[j] = uint16(i)` (`select.go:191-194`). Cases with nil
channels are OMITTED from the poll and lock orders entirely
(`select.go:173-177`). `cheaprandn` is Lemire's nearly-divisionless bounded
rand (`rand.go:291-294`) over the per-m PRNG.

**[ANALYSIS]** So "uniform pseudo-random" is realized as a genuinely uniform
permutation modulo (a) Lemire modulo bias (≤ 2^-32-scale, negligible) and (b)
`cheaprand` stream quality. But note: uniformity of the POLL ORDER gives
uniformity over ready cases only in pass 1 (all-ready case). When select
BLOCKS and is woken (pass 2), the chosen case is whichever channel's waiter
got signaled first — determined by the other goroutines' operation order,
not by fresh randomness. The spec's step-2 sentence only covers "one or more
of the communications can proceed" at decision time, so this is consistent;
an envelope should not promise per-wakeup re-randomization. Probe p14 (§4.16):
100k iterations of a two-ready-case select measured 50032/49968 (and
50034/49966 under -race) — consistent with uniform.

**[FACT]** Locking is deadlock-free by address order: `lockorder` is
heap-sorted by channel `sortkey()` (address) (`select.go:206-238`);
`sellock`/`selunlock` skip duplicate channels (`select.go:34-59`). Pass 1
walks `pollorder` looking for a ready case (`select.go:270-300`: recv case
checks waiting sender, then buffer, then closed; send case checks closed
FIRST — so a send case on a closed channel is "ready" and selecting it
panics, probe p23 §4.14); pass 2 enqueues a sudog on every channel in lock
order (`select.go:308-341`); on wakeup, all other sudogs are dequeued and the
losers discarded (`selectDone` CAS arbitration, `chan.go:905-916`).

### 3.6 Deadlock detector (`checkdead`, `proc.go:6363-6469`)

**[FACT]** "Check for deadlock situation. The check is based on number of
running M's, if 0 -> deadlock" (`proc.go:6363-6365`). Fires from the
scheduler when the last running M goes idle: if no M is running and every
non-system goroutine is `_Gwaiting`/`_Gpreempted` and no timers are pending,
`fatal("all goroutines are asleep - deadlock!")` (`proc.go:6468`). Special
cases: returns early for `-buildmode=c-shared`/`c-archive` (`proc.go:6374-6376`);
`grunning == 0` → `fatal("no goroutines (main called runtime.Goexit) - deadlock!")`
(`proc.go:6424-6427`); pending timers suppress it (`proc.go:6461-6466`).

**[ANALYSIS]** The detector is a WHOLE-PROGRAM check, not per-goroutine: it
fires only when EVERY goroutine is blocked on non-runtime-wakeable events. A
single leaked goroutine blocked forever is silent as long as any other
goroutine can run (and main's return exits the process regardless — probe
p17). `fatal` is not a panic: it is unrecoverable, prints
"fatal error: all goroutines are asleep - deadlock!" and exits with status 2.
Classification question for the arc: the detector is a RUNTIME SERVICE
diagnosing a state (global blockage) that the SPEC describes as "blocks
forever". Model the STATE (all-blocked = the program has no successor step —
a terminal stuck-in-blocked configuration, distinct from our fail-closed
`stuck`); treat the fatal-error report as the flagship implementation's
rendering of it (§6 row L6). The differential harness can rely on exit code 2
+ the message on this toolchain, but timers/background M's perturb WHEN it
fires, and under `-race` it does not fire at all (§5, probe run-race3).

### 3.7 Main return, goroutine leaks

**[FACT]** Probe p17 (§4.17): main returning kills everything immediately —
deferred functions in other goroutines do NOT run. No language-level
notification of goroutine death exists; leaks are silent (§3.6).

---

## 4. Edge-rule probe matrix (go1.26.5 linux/amd64, outputs verbatim)

Probe sources in `.tmp/conc-probes/`. "exit=N" is the wrapper-observed exit
status of `go run` (which forwards the program's own status as
"exit status 2" text for fatal errors/panics).

| # | probe | program essence | verbatim output |
|---|---|---|---|
| 4.1 | p01 | send on closed | `panic: send on closed channel` … `exit status 2` |
| 4.2 | p02 | close of closed | `panic: close of closed channel` … `exit status 2` |
| 4.3 | p03 | close of nil | `panic: close of nil channel` … `exit status 2` |
| 4.4a | p04 | send on nil (only goroutine) | `fatal error: all goroutines are asleep - deadlock!` + `goroutine 1 [chan send (nil chan)]` |
| 4.4b | p05 | recv on nil (only goroutine) | `fatal error: all goroutines are asleep - deadlock!` + `goroutine 1 [chan receive (nil chan)]` |
| 4.5 | p06 | close(buffered{10,20}); 4 receives | `10 true` / `20 true` / `0 false` / `0 false` / `len after close+drain: 0 cap: 3` |
| 4.6 | p07 | `range` over closed buffered {1,2,3} | `1` `2` `3` `range done` — range terminates at close-and-drained |
| 4.7 | p08 | select nil-chan case + default | `default taken: nil channel never ready` |
| 4.8 | p09 | `select {}` | `fatal error: all goroutines are asleep - deadlock!` + `goroutine 1 [select (no cases)]` |
| 4.9 | p10 | unbuffered self-send | `fatal error: all goroutines are asleep - deadlock!` + `goroutine 1 [chan send]` |
| 4.10 | p11 | `make(chan int, 0)` vs `make(chan int)` | `cap: 0` both; `cap-0 rendezvous ok` — cap-0 IS unbuffered (spec: "capacity … zero or absent" one rule) |
| 4.11 | p12 | comparison / map keys / chan-of-chan | `a==a: true a==c: true a==b: false nil==nil: true a==nil: false`; `map[a]: a map[c]: a map[b]: b len: 2`; `chan of chan roundtrip identity: true` |
| 4.12 | p13 | typed-nil chan in interface | `i == nil: false i == (chan int)(nil): true`; `assert ok: true v == nil: true` |
| 4.13 | p21 | `make(chan int, -1)` (non-constant) | `recovered: makechan: size out of range` — run-time panic, recoverable |
| 4.14 | p23 | select on closed chan: recv then send case | `recv case: 0 false`; `recovered: send on closed channel` — a send case on a closed channel counts as READY and panics when selected |
| 4.15 | p24 | close wakes a blocked sender | `sender recovered: send on closed channel` / `main done` — the panic is raised IN the sender goroutine, recoverable there |
| 4.16 | p14 | 100k two-ready-case selects | `a: 50032 b: 49968` (plain); `a: 50034 b: 49966` (-race) |
| 4.17 | p17 | main returns with sleeping goroutines | `main returns immediately` only — goroutine bodies AND their defers never run |
| 4.18 | p15 | len/cap probes | `nil chan len: 0 cap: 0`; `buffered len: 2 cap: 5`; `unbuffered len: 0 cap: 0` |
| 4.19 | p16 | range over never-closed drained chan | prints `1` `2` then `fatal error: all goroutines are asleep - deadlock!` `[chan receive]` |
| 4.20 | p18 | buffer FIFO through blocked sender (cap 4, 5th send blocks, then drain) | `order received: [1 2 3 4 5]` |
| 4.21 | p19 | 5 receivers block in order 0..4; 5 sends | `wakeup order (block order was 0,1,2,3,4): [0 1 2 3 4]` — FIFO waiter wakeup observed (implementation, NOT spec; §6 row L4) |
| 4.22 | p25 | select with only nil channels, no default | `fatal error: all goroutines are asleep - deadlock!` + `goroutine 1 [select]` |
| 4.23 | p26 | concurrent len/cap vs send/recv under `-race` | `ok; observed sum: true`, exit=0 — race detector does NOT flag len/cap concurrent with channel ops (consistent with spec §1.1) |

**[ANALYSIS]** Notable classifications:
- Nil-channel ops and empty/all-nil selects are BLOCK-FOREVER per spec; the
  "deadlock!" fatal error is the runtime's whole-program detector (§3.6)
  firing because nothing else could run — with another live goroutine these
  programs simply hang (verified implicitly by p24/p19 structure).
- The wait-reason strings in the fatal-error dump (`[chan send (nil chan)]`,
  `[select (no cases)]` etc.) are diagnostic detail, not behavior to model.
- p18+p21 pin buffer-FIFO-through-pressure and make-negative-size panic,
  both needed as corpus guardrail cases.
- p12's `map[c]: a` (alias keys) pins reference-identity as map-key equality.

---

## 5. The race detector as an oracle

**[FACT]** Mechanism: ThreadSanitizer, per go_mem.html:226-228 ("Implementations
using ThreadSanitizer (accessed with 'go build -race') do exactly this" —
report and halt). It is a DYNAMIC happens-before checker (vector clocks over
the synchronization operations actually executed).

**[FACT]** Probed behavior (probe p20: unsynchronized write/write then
channel-synchronized read):
- `go run -race p20_race.go` prints the standard report
  (`WARNING: DATA RACE` / `Write at 0x… by goroutine 8` / `Previous write at
  0x… by main goroutine` / `Found 1 data race(s)`) and go run reports
  `exit status 66`.
- Direct binary: exit code **66** (default), **99** under
  `GORACE=exitcode=99` — configurable.
- `GORACE=halt_on_error=1`: exits at first race (the program's own
  `x = …` output is suppressed); default continues execution and exits
  nonzero at process end.
- Race-free program under `-race`: exit 0, no report (probe p06race).
- **Deadlock detector does NOT fire under `-race`**: p10 (self-send) and p09
  (`select {}`) compiled with `-race` hang past a 20s timeout (exit=124 via
  `timeout`) where the plain builds fatal-error immediately. [ANALYSIS:
  presumably the TSan background thread keeps an M alive so `checkdead`'s
  running-M count never reaches zero; mechanism unverified, behavior
  reproducible 2/2.] Consequence: the differential harness must not combine
  `-race` with deadlock-expectation cases.

**[FACT — guarantee/limits]** By construction a dynamic HB detector reports
only races between operations that actually executed in the observed
interleaving: no false positives w.r.t. the HB model (a report is a real
HB-unordered conflicting pair in THAT execution), but false NEGATIVES on
unexercised interleavings/paths are inherent. **[ANALYSIS]** So `-race` is a
sound-but-incomplete oracle for the DRF precondition: a report ⇒ the program
is outside our supported envelope (fail closed with confidence); silence ⇒
nothing (the corpus cannot use "-race clean" as evidence of DRF). This is
exactly the doctrine's "too-wide direction has no oracle" shape, one level
up: the racy/DRF boundary itself is only semi-decidable by testing.

**[FACT]** Cost/knobs observed: `-race` builds run the interpreter probes
~unchanged in outcome (p14 distribution unaffected). Scheduling-perturbation
probes on the race-free nondeterministic program p22 (two goroutines send
"A"/"B", main receives both): **40/40 runs printed `BA`** under each of
{default GOMAXPROCS, GOMAXPROCS=1, GOMAXPROCS=1 + GODEBUG=asyncpreemptoff=1}.
**[ANALYSIS]** The flagship scheduler is far more deterministic than its
envelope: `go run` NEVER exhibited `AB` in 120 runs even though `AB` is
plainly legal (start order vs run order is unpinned). Direct empirical
confirmation of the doctrine's central claim — the oracle cannot exhibit the
envelope's width, so too-wide envelope statements are checkable only by
review against spec text, and differential agreement on nondeterministic
observables is sanity-checking, not verification. (Go's own randomization —
select shuffle, map iteration — covers only the latitudes the runtime chose
to randomize; goroutine wakeup/run order is not one of them.)

---

## 6. LATITUDE INVENTORY — the envelope raw material

Each row: the latitude, the text that BOUNDS it (the envelope's outer edge),
what the flagship implementation actually does (one legal point inside), and
the modeling consequence. Rows marked (omission) have no marked spec keyword —
the latitude exists because no text constrains it.

| # | Latitude point | Bounding text (verbatim anchor) | go1.26.5 realization | Modeling consequence |
|---|---|---|---|---|
| L1 | **Goroutine scheduling order / interleaving** (omission) | Spec is silent on scheduling entirely (§1.2). Memory model bounds observations: DRF programs "behave as if all the goroutines were multiplexed onto a single processor" (`go_mem.html:53-55`); blocking rules of §1.3-1.5 constrain which schedules are enabled. | M:N scheduler, work stealing, runnext LIFO slot; empirically near-deterministic on small programs (p22: 120/120 same order) | The `Choices` stream's largest consumer: interleaving choice at every scheduler-visible step. Envelope = ALL enabled-step interleavings. No fairness assumption is available from spec text; liveness claims need explicitly-added fairness premises. |
| L2 | **Select choice among ready cases** | "chosen via a uniform pseudo-random selection" (`go_spec.html:6995`) | Fisher–Yates pollorder via `cheaprandn` (`select.go:191-194`); measured 50.03/49.97 over 100k (§4.16) | Choice-stream consumption site. Possibilistic envelope (any ready case) is sound but deliberately DROPS the spec's uniformity (distributional claims are unprovable in a possibilistic model — record the weakening). The blocked-then-woken path is NOT re-randomized (§3.5): woken case = whichever communication arrived, which is L1 latitude, not L2. |
| L3 | **Buffered-channel element order** | NOT latitude — "Channels act as first-in-first-out queues" (`go_spec.html:1760-1767`) is spec | Circular buffer; FIFO preserved even through full-buffer blocked-sender handoff (`chan.go:714-736`, probe p18) | Model FIFO exactly; no envelope needed. Cross-SENDER enqueue order is L1 latitude (which send commits first), but once committed, order is pinned. |
| L4 | **Waiter wakeup order** (multiple blocked senders or receivers; omission) | No spec text at all. Memory model only gives per-pairing HB rules ("A send … is synchronized before … the corresponding receive", `go_mem.html:372-375`) — it never says WHICH blocked waiter pairs with the next op. | sudog queues are FIFO (`chan.go:872-919`; probe p19: wakeup order = block order), modulo select-loser skipping | Envelope: the next operation may pair with ANY blocked waiter (choice-stream site) — FIFO-wakeup is implementation, and programs relying on it are relying on latitude. Cheap to model possibilistically; the strict lane will still match go run because the flagship is FIFO. |
| L5 | **Racy-program outcomes** | "An implementation may always react to a data race by reporting the race and terminating the program. Otherwise, each read of a single-word-sized or sub-word-sized memory location must observe a value actually written to that location … and not yet overwritten" + multiword "arbitrary memory corruption" (`go_mem.html:60-74`, `255-273`) | TSan report + exit 66 under `-race`; undetected otherwise; word-tearing per hardware | FAIL CLOSED. No semantics assigned below the DRF line (§2.2 analysis): the envelope would need torn values + corruption, which no theorem consumer wants. DRF precondition must be surfaced as an explicit assumption/side-condition of concurrency theorems. |
| L6 | **Deadlock detection & timing** (omission) | Spec says only "blocks forever" (`go_spec.html:6084`, `5312`, `7020-7022`). No text mandates detection. | `checkdead`: whole-program all-asleep check → `fatal("all goroutines are asleep - deadlock!")`, exit 2 (`proc.go:6468`); suppressed by pending timers, c-shared/c-archive, and (observed) `-race` builds | Model the STATE (no enabled step ⇒ terminal all-blocked configuration), not the report. The fatal error is one legal rendering of "blocks forever" (terminating with a diagnostic is compatible with an implementation's freedom to crash a wedged process — but note: the SPEC never licenses it; this is the flagship's choice observable in the differential). Harness: expect message+exit 2 on this toolchain; never in `-race` runs. |
| L7 | **len(ch) under concurrency** | Legal without synchronization (`go_spec.html:1757-1760`); value = "number of elements queued in channel buffer" (`go_spec.html:7627`) at an unspecified instant (omission) | Unlocked read of `qcount`; not flagged by TSan (probe p26) | len/cap on a concurrently-used channel is a SNAPSHOT choice (which instant) — an L1-derived latitude, not a separate stream site if channel ops are atomic interpreter steps: the snapshot is pinned by where the len step lands in the interleaving. Sequential programs: fully deterministic. |
| L8 | **Goroutine leaks / exit visibility** (omission) | "When that function invocation returns, the program exits. It does not wait for other (non-main) goroutines to complete" (`go_spec.html:8388-8391`); "The exit of a goroutine is not guaranteed to be synchronized before any event" (`go_mem.html:335-338`) | Immediate process exit; leaked goroutines silent; their defers never run (probe p17) | Main-return is a program-terminating step that discards all other goroutines (and their defers) with no observable. Leaks need no modeling — but any "all effects happened" claim must be scoped to HB-before-main-return effects. |
| L9 | **Panic identity for runtime errors** | "The exact error values that represent distinct run-time error conditions are unspecified" (`go_spec.html:8426`) | `plainError("send on closed channel")` etc. (`chan.go:226,416,425`); `makechan: size out of range` (`chan.go:88`) | Match the repo's existing runtime-panic treatment: model THAT a run-time panic occurs (recoverable, probes p21/p23/p24); the message strings are differential-harness detail, not semantic identity. |
| L10 | **make(chan) implementation limits** | "The implementation guarantees that [len/cap] always fits into an int" (`go_spec.html:7616`); size "must be non-negative and representable by a value of type int," negative ⇒ run-time panic (`go_spec.html:7721-7726`) | `makechan` also panics on total allocation overflow (`mem > maxAlloc`, `chan.go:85-89`) — an implementation resource limit beyond the spec's negativity rule | Negative size ⇒ panic is spec, model it. Allocation-limit panics are resource latitude — out of semantic scope (same stance as OOM elsewhere). |
| L11 | **Mutex/TryLock spurious failure** (out of arc scope, recorded) | "l.TryLock … may be considered to be able to return false even when the mutex l is unlocked" (`go_mem.html:540-545`) | best-effort CAS | If sync primitives ever enter scope: TryLock needs a choice-stream site by the memory model's own text. |

**[ANALYSIS] Consolidated: the concurrency `Choices` consumption sites are
exactly three** — (1) interleaving choice / who steps next (L1, subsumes L7,
L8's timing), (2) select choice among simultaneously-ready cases (L2), (3)
waiter-pairing choice when multiple goroutines are blocked on the same
channel side (L4). L3 (buffer FIFO) is deterministic spec behavior; L5 is
fail-closed, not enveloped; L6 is a terminal-state classification; L9/L10
follow existing repo doctrine. Everything the arc must model or refuse
reduces to: the §1.3-1.6 transition rules (deterministic given a choice),
these three choice sites, the L5 DRF precondition, and the L6 terminal state.

---

## 7. Surprises and open questions for the arc

1. **Deadlock detector is disabled (observed) under `-race`** (§5). Direct
   harness impact: deadlock-expectation corpus cases and race-instrumented
   runs cannot be combined. Mechanism unverified ([ANALYSIS] only).
2. **Select's blocked path does not re-randomize** (§3.5): "uniform
   pseudo-random" applies only at entry among already-ready cases. An
   envelope statement phrased as "select uniformly among ready cases at
   commit time" would be WRONG for the wakeup path; phrase as "any ready
   case may be chosen" (entry) + waiter-pairing latitude (wakeup).
3. **Send case on a closed channel is 'ready' in select** and selecting it
   panics (probe p23) — an easy edge to miss in a select model; the
   pass-1 check order (`select.go:289-292`) makes closed-send eligible for
   selection even when another case is also ready.
4. **A close wakes blocked senders into a panic IN THE SENDER's goroutine**
   (probe p24, `chan.go:460-476`, `chan.go:303-308`) — the panic site is the
   blocked send statement, recoverable there, NOT at the close site.
5. **The flagship scheduler's determinism** (p22: 120/120 identical) is
   direct evidence that differential green on nondeterministic observables is
   weak — the strict lane's choice-invariance requirement (nondeterminism
   doctrine) is doing real work here.
6. **Buffer FIFO survives blocked-sender pressure** via the head-out/tail-in
   same-slot trick (probe p18) — a good adversarial corpus case for any
   interpreter that models the buffer + waiters separately.
7. `cap=0 ⟺ unbuffered` is a single spec rule, not two channel kinds
   (`go_spec.html:1730-1734`, probe p11) — the model needs no
   unbuffered/buffered type split, only a capacity value.
