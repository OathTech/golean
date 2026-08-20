# Go scheduling semantics: what may a conforming program assume?

[synthesis] Evidence dossier for the GoCore scheduler model. Research cutoff: 2026-08-20.

## Scope, labels, and version pin

[implementation @go1.26.7] The latest Go 1.26 patch at the cutoff is **go1.26.7**, released 2026-08-19. The official history says: “go1.26.7 (released 2026-08-19) includes fixes to the `net/http` package.” ([release history](https://go.dev/doc/devel/release#go1.26.minor); tag commit [`e3336a22ad3f0a90bd252c95d8b5544e02674205`](https://github.com/golang/go/commit/e3336a22ad3f0a90bd252c95d8b5544e02674205)).

[implementation @go1.26.7] The workspace's Go mirror ends at go1.26.6, commit [`1ea5a71ad8ceb7b9f16b4b6f8ea4739a4327dd6e`](https://github.com/golang/go/commit/1ea5a71ad8ceb7b9f16b4b6f8ea4739a4327dd6e). I compared SHA-256 hashes of `runtime/{preempt.go,proc.go,chan.go,signal_unix.go,os_windows.go,os_wasm.go,os_plan9.go,extern.go,debug.go,panic.go,mgc.go}` and `sync/{rwmutex.go,cond.go}` from that commit with the same files served from the go1.26.7 tag; all thirteen are byte-identical. Source-line citations below therefore use the go1.26.7 commit and were inspected locally in the identical go1.26.6 files.

[synthesis] The labels mean:

- `[normative]`: language specification, memory model, Go 1 compatibility policy, or a standard-library API contract.
- `[maintainer]`: an identifiable Go maintainer's statement, an accepted Go design, or official Go-project explanatory material such as a release note or FAQ. This is evidence of intent or history, not automatically a language guarantee.
- `[implementation @version]`: observed gc/runtime code at the pinned version.
- `[secondary]`: papers, verification systems, or other non-Go-project analysis.

[synthesis] “No guarantee” findings below rest on both positive evidence (the Go project expressly says the scheduler is unspecified) and a search of the pinned specification and current memory model. The specification contains no occurrence of `schedul`, `preempt`, `fair`, or `starv`; the scheduling-adjacent normative passages are quoted below.

[synthesis] Exhaustiveness is strongest for the language specification and memory model, both of which were full-text audited. For standard-library documentation, the dossier covers exported `runtime` scheduling-control contracts and `sync` clauses that expressly discuss progress or priority; it does not attempt to reproduce every API sentence saying that a particular call may block.

## 1. Preemption points, de jure

### 1.1 Direct answer

[synthesis] No normative Go language text constrains the instruction or source-code points at which an implementation may switch away from a running goroutine. The language specifies sequential execution within a goroutine, creation of a concurrent goroutine, when channel operations must block or can proceed, and how a ready `select` case is chosen. It does **not** specify a scheduler, a timeslice, call/loop/channel “yield points,” asynchronous preemption, or a prohibition on switching between any two source operations.

[maintainer] The clearest official historical statement is the Go 1.5 release note:

> In Go 1.5, the order in which goroutines are scheduled has been changed. The properties of the scheduler were never defined by the language, but programs that depend on the scheduling order may be broken by this change. We have seen a few (erroneous) programs affected by this change. If you have programs that implicitly depend on the scheduling order, you will need to update them.

([Go 1.5 release notes, “Runtime”](https://go.dev/doc/go1.5#runtime))

[maintainer] Ian Lance Taylor answered the same question directly:

> The answer to that question is that there are no guarantees. The
> goroutine scheduler is not described in the language spec. Different
> implementations may act differently.

[maintainer] He continued:

> At this point I don't think it would be appropriate to say anything
> about the goroutine scheduler in the language spec. Anything that we
> could say would be so anodyne as to mean nothing. It would not help
> anybody when writing any actual Go program, nor would it help anybody
> when writing any actual Go implementation. So there seems little
> point to saying anything.

([golang-nuts, 2014-06-16](https://groups.google.com/g/golang-nuts/c/PWt4r9b40bc), lines shown in the archived message headed “Ian Lance Taylor,” beginning “You are phrasing your question about channels”)

### 1.2 What the language specification actually says

[normative] A `go` statement creates concurrency but says nothing about when the new goroutine is scheduled:

> A "go" statement starts the execution of a function call
> as an independent concurrent thread of control, or *goroutine*,
> within the same address space.

> The function value and parameters are
> evaluated as usual
> in the calling goroutine, but
> unlike with a regular call, program execution does not wait
> for the invoked function to complete.
> Instead, the function begins executing independently
> in a new goroutine.
> When the function terminates, its goroutine also terminates.

([Go 1.26.7 specification, `Go statements`, `doc/go_spec.html:6910`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/doc/go_spec.html#L6910))

[normative] Channel readiness and blocking are specified:

> If the capacity is zero or absent, the channel is unbuffered and communication
> succeeds only when both a sender and receiver are ready. Otherwise, the channel
> is buffered and communication succeeds without blocking if the buffer
> is not full (sends) or not empty (receives).
> A `nil` channel is never ready for communication.

([Go 1.26.7 specification, `Channel types`, `doc/go_spec.html:1739`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/doc/go_spec.html#L1739))

[normative] Receive:

> The expression blocks until a value is available.
> Receiving from a `nil` channel blocks forever.
> A receive operation on a closed channel can always proceed
> immediately, yielding the element type's zero value
> after any previously sent values have been received.

([Go 1.26.7 specification, `Receive operator`, `doc/go_spec.html:5303`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/doc/go_spec.html#L5303))

[normative] Send:

> Both the channel and the value expression are evaluated before communication
> begins. Communication blocks until the send can proceed.
> A send on an unbuffered channel can proceed if a receiver is ready.
> A send on a buffered channel can proceed if there is room in the buffer.
> A send on a closed channel proceeds by causing a run-time panic.
> A send on a `nil` channel blocks forever.

([Go 1.26.7 specification, `Send statements`, `doc/go_spec.html:6077`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/doc/go_spec.html#L6077))

[normative] FIFO is a property of values already sent, not a rule choosing among competing goroutines:

> A single channel may be used in
> send statements,
> receive operations,
> and calls to the built-in functions
> `cap` and
> `len`
> by any number of goroutines without further synchronization.
> Channels act as first-in-first-out queues.
> For example, if one goroutine sends values on a channel
> and a second goroutine receives them, the values are
> received in the order sent.

([Go 1.26.7 specification, `Channel types`, `doc/go_spec.html:1757`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/doc/go_spec.html#L1757))

[maintainer] Ian Lance Taylor expressly separated FIFO from scheduling among blocked senders:

> No, it's not.
> That is a scheduling question. When there are multiple goroutines
> waiting to send on an unbuffered channel, and a different goroutine
> executes a receive operation on that channel, which of the sending
> goroutines gets to execute? The language does not specify.

([golang-nuts, 2014-06-16](https://groups.google.com/g/golang-nuts/c/PWt4r9b40bc))

[normative] `select` has the only general-looking choice rule, but it governs communications ready at one execution of a `select`, not runnable-goroutine scheduling over time:

> If one or more of the communications can proceed,
> a single one that can proceed is chosen via a uniform pseudo-random selection.
> Otherwise, if there is a default case, that case is chosen.
> If there is no default case, the "select" statement blocks until
> at least one of the communications can proceed.

([Go 1.26.7 specification, `Select statements`, `doc/go_spec.html:6993`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/doc/go_spec.html#L6993))

[synthesis] This is a per-choice distributional constraint. It is not a weak- or strong-fairness axiom: the specification says neither that draws are independent nor that a continuously enabled case must eventually win. For safety verification, nondeterministic selection among ready cases over-approximates the specified outcomes; for probabilistic/liveness verification, replacing it with demonic choice discards the specified uniform distribution and must be documented as an abstraction.

[normative] Initialization has one explicit sequencing rule and permits concurrent goroutines:

> Package initialization—variable initialization and the invocation of
> `init` functions—happens in a single goroutine,
> sequentially, one package at a time.
> An `init` function may launch other goroutines, which can run
> concurrently with the initialization code. However, initialization
> always sequences
> the `init` functions: it will not invoke the next one
> until the previous one has returned.

([Go 1.26.7 specification, `Program initialization`, `doc/go_spec.html:8362`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/doc/go_spec.html#L8362))

[normative] Program exit can strand otherwise runnable goroutines:

> When that function invocation returns, the program exits.
> It does not wait for other (non-`main`) goroutines to complete.

([Go 1.26.7 specification, `Program execution`, `doc/go_spec.html:8387`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/doc/go_spec.html#L8387))

### 1.3 What the memory model says—and does not say

[normative] The memory model's subject is observation, not scheduling:

> The Go memory model specifies the conditions under which reads of a variable in one goroutine can be guaranteed to observe values produced by writes to the same variable in a different goroutine.

([Go memory model, version of 2022-06-06](https://go.dev/ref/mem))

[normative] Its “single processor” sentence is DRF-SC, not a progress promise:

> In the absence of data races, Go programs behave as if all the goroutines were multiplexed onto a single processor.

> This property is sometimes referred to as DRF-SC: data-race-free programs execute in a sequentially consistent manner.

([Go memory model, `Informal Overview`](https://go.dev/ref/mem))

[normative] The formal execution requirements constrain operations that occur, not which enabled goroutine must contribute a next operation:

> A goroutine execution is modeled as a set of memory operations executed by a single goroutine.

> Requirement 1: The memory operations in each goroutine must correspond to a correct sequential execution of that goroutine, given the values read from and written to memory. That execution must be consistent with the sequenced before relation, defined as the partial order requirements set out by the Go language specification for Go's control flow constructs as well as the order of evaluation for expressions.

> A Go program execution is modeled as a set of goroutine executions, together with a mapping W that specifies the write-like operation that each read-like operation reads from. (Multiple executions of the same program can have different program executions.)

([Go memory model, `Memory Model`](https://go.dev/ref/mem))

[synthesis] No progress, maximality, fairness, or “enabled operation eventually occurs” premise appears in Requirements 1–3. DRF-SC restricts the explanation of completed memory operations; it does not require a fair interleaving.

[normative] Goroutine creation establishes an ordering edge:

> The `go` statement that starts a new goroutine is synchronized before the start of the goroutine's execution.

[normative] The following example sentence sounds temporal:

> calling `hello` will print `"hello, world"` at some point in the future (perhaps after `hello` has returned).

([Go memory model, `Goroutine creation`](https://go.dev/ref/mem))

[synthesis] Read narrowly, the first sentence says that **if** the child starts, creation precedes its start. The example's “will … at some point” is the only liveness-sounding sentence found in the memory model. It should not be elevated into a general scheduler-fairness axiom: it is an explanatory example in a document whose formal requirements contain no progress premise; `main` may exit without waiting; and maintainers explicitly say the language permits starvation. This tension is worth recording rather than silently normalizing.

[normative] Goroutine destruction is explicitly weak:

> The exit of a goroutine is not guaranteed to be synchronized before any event in the program.

> the assignment to `a` is not followed by any synchronization event, so it is not guaranteed to be observed by any other goroutine. In fact, an aggressive compiler might delete the entire `go` statement.

> If the effects of a goroutine must be observed by another goroutine, use a synchronization mechanism such as a lock or channel communication to establish a relative ordering.

([Go memory model, `Goroutine destruction`](https://go.dev/ref/mem))

[normative] The compatibility policy makes unspecified behavior non-portable:

> Unspecified behavior. The Go specification tries to be explicit about most properties of the language, but there are some aspects that are undefined. Programs that depend on such unspecified behavior may break in future releases.

([Go 1 compatibility policy](https://go.dev/doc/go1compat#expectations))

### 1.4 Exported runtime API constraints

[normative] `runtime.Gosched` is the one exported operation whose contract expressly yields execution:

> Gosched yields the processor, allowing other goroutines to run. It does not suspend the current goroutine, so execution resumes automatically.

([Go 1.26.7 `src/runtime/proc.go:385-386`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/proc.go#L385-L386))

[normative] `runtime.GOMAXPROCS` constrains simultaneous execution, not scheduling order or progress:

> GOMAXPROCS sets the maximum number of CPUs that can be executing
> simultaneously and returns the previous setting. If n < 1, it does not change
> the current setting.

([Go 1.26.7 `src/runtime/debug.go:12-14`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/debug.go#L12-L14))

[normative] `runtime.LockOSThread` supplies a placement guarantee, but not uninterrupted execution or priority:

> LockOSThread wires the calling goroutine to its current operating system thread.
> The calling goroutine will always execute in that thread,
> and no other goroutine will execute in it,
> until the calling goroutine has made as many calls to
> UnlockOSThread as to LockOSThread.
> If the calling goroutine exits without unlocking the thread,
> the thread will be terminated.

> All init functions are run on the startup thread. Calling LockOSThread
> from an init function will cause the main function to be invoked on
> that thread.

([Go 1.26.7 `src/runtime/proc.go:5607-5617`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/proc.go#L5607-L5617))

[normative] `runtime.Goexit` makes a narrow program-lifetime promise distinct from `main` returning:

> Calling Goexit from the main goroutine terminates that goroutine
> without func main returning. Since func main has not returned,
> the program continues execution of other goroutines.
> If all other goroutines exit, the program crashes.

([Go 1.26.7 `src/runtime/panic.go:676-679`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/panic.go#L676-L679))

[normative] `runtime.GC` is permitted to stop all user execution, but gives no scheduling order after that stop:

> GC runs a garbage collection and blocks the caller until the
> garbage collection is complete. It may also block the entire
> program.

([Go 1.26.7 `src/runtime/mgc.go:519-521`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/mgc.go#L519-L521))

[synthesis] These are real API-level constraints a GoCore model should preserve if it models `runtime`, but none identifies implicit preemption points or promises that a runnable goroutine eventually runs.

## 2. Preemption points, de facto in gc go1.26.7

### 2.1 The three implementation safe-point classes

[implementation @go1.26.7] `runtime/preempt.go` states the implementation model verbatim:

> A goroutine can be preempted at any safe-point. Currently, there
> are a few categories of safe-points:
>
> 1. A blocked safe-point occurs for the duration that a goroutine is
>    descheduled, blocked on synchronization, or in a system call.
>
> 2. Synchronous safe-points occur when a running goroutine checks
>    for a preemption request.
>
> 3. Asynchronous safe-points occur at any instruction in user code
>    where the goroutine can be safely paused and a conservative
>    stack and register scan can find stack roots. The runtime can
>    stop a goroutine at an async safe-point using a signal.

([`src/runtime/preempt.go:5-19`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/preempt.go#L5-L19))

[implementation @go1.26.7] Synchronous preemption is the function-prologue/stack-check mechanism:

> Synchronous safe-points are implemented by overloading the stack
> bound check in function prologues. To preempt a goroutine at the
> next synchronous safe-point, the runtime poisons the goroutine's
> stack bound to a value that will cause the next stack bound check
> to fail and enter the stack growth implementation, which will
> detect that it was actually a preemption and redirect to preemption
> handling.

([`src/runtime/preempt.go:27-33`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/preempt.go#L27-L33))

[implementation @go1.26.7] Async preemption suspends the OS thread, validates the stopped PC, and injects `asyncPreempt`:

> If all conditions are
> satisfied, it adjusts the signal context to make it look like the
> signaled thread just called asyncPreempt and resumes the thread.
> asyncPreempt spills all registers and enters the scheduler.

([`src/runtime/preempt.go:35-43`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/preempt.go#L35-L43))

[implementation @go1.26.7] `asyncPreempt2` marks the async safe point and either parks for a stop request or calls `gopreempt_m`, which returns the G to scheduling ([`src/runtime/preempt.go:295-343`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/preempt.go#L295-L343)).

### 2.2 Explicit and cooperative scheduling points

[normative] The `runtime.Gosched` API contract is:

> Gosched yields the processor, allowing other goroutines to run. It does not suspend the current goroutine, so execution resumes automatically.

([Go 1.26.7 `src/runtime/proc.go:385-386`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/proc.go#L385-L386))

[implementation @go1.26.7] The implementation changes the current G from `_Grunning` to `_Grunnable`, puts it on the global run queue (unless this was an STW preemption), and calls `schedule` ([`src/runtime/proc.go:4307-4345`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/proc.go#L4307-L4345)). This is a genuine yield, but neither the API nor the code promises which other runnable G runs, that every other G runs, or a time bound before this G resumes.

[implementation @go1.26.7] A channel send that cannot proceed queues a `sudog` and calls `gopark` ([`src/runtime/chan.go:257-283`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/chan.go#L257-L283)); a receive with no sender does likewise ([`src/runtime/chan.go:636-667`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/chan.go#L636-L667)). Those blocking paths deschedule the current G.

[implementation @go1.26.7] A channel operation that completes need not yield the current G. For example, direct send copies to the waiting receiver, calls `goready(gp, ...)`, and returns to the sender ([`src/runtime/chan.go:312-350`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/chan.go#L312-L350)). `goready` makes the peer runnable; it is not an immediate handoff guarantee.

[synthesis] Therefore “channel operations are preemption/yield points” is only conditionally true. A blocking operation parks; a ready operation may merely make another G runnable and continue. A model that forces a switch at every channel operation is narrower than gc and is not language-derived.

### 2.3 What cannot be asynchronously preempted

[implementation @go1.26.7] The current M must have no runtime locks, not be allocating, have no `preemptoff` reason, own a running P, have a current G, and not have that G in `_Gsyscall`:

> `return mp.locks == 0 && mp.mallocing == 0 && mp.preemptoff == "" && mp.p.ptr().status == _Prunning && mp.curg != nil && readgstatus(mp.curg)&^_Gscan != _Gsyscall`

([`src/runtime/preempt.go:284-290`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/preempt.go#L284-L290))

[implementation @go1.26.7] `isAsyncSafePoint` rejects:

- a non-user G or unsuitable M state ([`preempt.go:393-403`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/preempt.go#L393-L403));
- insufficient stack space ([`preempt.go:405-408`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/preempt.go#L405-L408));
- with `GOEXPERIMENT=RuntimeSecret`, a G inside a secret computation, because conservative scanning or saving registers could copy secrets ([`preempt.go:410-424`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/preempt.go#L410-L424));
- a PC that is not Go code ([`preempt.go:426-430`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/preempt.go#L426-L430));
- compiler-marked unsafe points, including “atomic sequences (e.g., write barrier) and nosplit functions (except at calls)” ([`preempt.go:443-449`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/preempt.go#L443-L449));
- assembly or a function without a locals pointer map ([`preempt.go:450-458`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/preempt.go#L450-L458));
- functions whose innermost name begins `runtime.`, `internal/runtime/`, or `reflect.` ([`preempt.go:460-482`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/preempt.go#L460-L482)).

[implementation @go1.26.7] Restartable unsafe sequences are handled by backing the resume PC up to a safe start, not by stopping in their middle ([`src/runtime/preempt.go:484-496`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/preempt.go#L484-L496)).

[implementation @go1.26.7] Async preemption support is platform-specific: Unix and Windows set `preemptMSupported = true` ([`signal_unix.go:361`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/signal_unix.go#L361), [`os_windows.go:1146`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/os_windows.go#L1146)); Plan 9 and wasm set it to false ([`os_plan9.go:550-555`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/os_plan9.go#L550-L555), [`os_wasm.go:137-140`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/os_wasm.go#L137-L140)). The wasm lock files are blunter: “There is no preemption.” ([`lock_js.go:14`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/lock_js.go#L14), [`lock_wasip1.go:9`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/lock_wasip1.go#L9)). This means no signal-based async preemption; blocking/cooperative scheduling still exists.

[implementation @go1.26.7] `GODEBUG=asyncpreemptoff=1` disables signal-based async preemption:

> This makes some loops
> non-preemptible for long periods, which may delay GC and
> goroutine scheduling.

([`src/runtime/extern.go:227-232`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/extern.go#L227-L232))

### 2.4 How a preemption request is generated—and why 10 ms is not a bound

[implementation @go1.26.7] The monitor thread sleeps from 20 μs up to 10 ms and stays active to “preempt long running G's” ([`src/runtime/proc.go:6478-6513`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/proc.go#L6478-L6513)). `forcePreemptNS` is 10 ms, described as “the time slice given to a G before it is preempted” ([`proc.go:6626-6628`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/proc.go#L6626-L6628)). `retake` calls `preemptone` when a P has retained the same `schedtick` for that duration, including a chain of `runnext` Gs sharing one slice ([`proc.go:6656-6671`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/proc.go#L6656-L6671)).

[implementation @go1.26.7] The request path expressly disclaims reliability:

> This function is purely best-effort. It can incorrectly fail to inform the
> goroutine. It can inform the wrong goroutine. Even if it informs the
> correct goroutine, that goroutine might ignore the request if it is
> simultaneously executing newstack.

> The actual preemption will happen at some point in the future

([`src/runtime/proc.go:6856-6865`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/proc.go#L6856-L6865)). The function also falls back to only poisoning the stack guard when the platform lacks async support or `asyncpreemptoff` is set ([`proc.go:6880-6892`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/proc.go#L6880-L6892)).

[synthesis] Thus 10 ms is an implementation threshold for attempting preemption, not a maximum scheduling latency, a maximum uninterrupted run, or a portable promise.

### 2.5 Async-preemption design and CL history

[maintainer] The accepted design begins:

> Go currently uses compiler-inserted cooperative preemption points in
> function prologues.

[maintainer] The design explicitly places the problem outside the language:

> And because this is a language implementation issue that exists
> outside of Go's language semantics, these failures are surprising and
> very difficult to debug.

[maintainer] It proposed:

> non-cooperative preemption, which would allow goroutines to be preempted at
> essentially any point without the need for explicit preemption checks.

([proposal `24543-non-cooperative-preemption.md:1-41`, pinned proposal commit `0be13090fdb0cbae0d71641bb676d924bc1c94de`](https://github.com/golang/proposal/blob/0be13090fdb0cbae0d71641bb676d924bc1c94de/design/24543-non-cooperative-preemption.md#L1-L41); issue [#24543](https://github.com/golang/go/issues/24543))

[maintainer] The design records the old envelope:

> Up to and including Go 1.10, Go has used cooperative preemption with
> safe-points only at function calls (and even then, not if the function
> is small or gets inlined).

[maintainer] It identifies the liveness failure:

> In really extreme cases, it can cause a program to halt, such as
> when a goroutine spinning on an atomic load starves out the
> goroutine responsible for setting that atomic.

([proposal lines 44–92](https://github.com/golang/proposal/blob/0be13090fdb0cbae0d71641bb676d924bc1c94de/design/24543-non-cooperative-preemption.md#L44-L92))

[maintainer] The implemented conservative-inner-frame design says:

> If a goroutine is interrupted at a point that must be GC atomic ... the runtime can simply let the goroutine resume and try again later.

[maintainer] The same design adds:

> Neither stack scan preemption nor scheduler preemption have tight time
> bounds, so the runtime can wait for a cooperative preemption before
> falling back to non-cooperative preemption.

([`conservative-inner-frame.md:23-48`](https://github.com/golang/proposal/blob/0be13090fdb0cbae0d71641bb676d924bc1c94de/design/24543/conservative-inner-frame.md#L23-L48), [`:74-80`](https://github.com/golang/proposal/blob/0be13090fdb0cbae0d71641bb676d924bc1c94de/design/24543/conservative-inner-frame.md#L74-L80))

[maintainer] The rejected/alternative “safe-points everywhere” subdesign is still useful for boundaries:

> Certain instructions cannot be safe-points, so if a signal occurs at
> such a point, the runtime would simply resume the thread and try again
> later.
> The compiler just needs to make *most* instructions safe-points.

[maintainer] The same subdesign adds:

> By default, the runtime cannot safely preempt assembly
> code since it won't know what registers contain pointers.

([`safe-points-everywhere.md:23-40`](https://github.com/golang/proposal/blob/0be13090fdb0cbae0d71641bb676d924bc1c94de/design/24543/safe-points-everywhere.md#L23-L40), [`:181-189`](https://github.com/golang/proposal/blob/0be13090fdb0cbae0d71641bb676d924bc1c94de/design/24543/safe-points-everywhere.md#L181-L189))

[implementation @history] Core Go 1.14 CLs, with permanent commit IDs:

- CL [201757](https://go-review.googlesource.com/c/go/+/201757), commit [`40b74558771ba9db493728dcaabe43318daf9b97`](https://github.com/golang/go/commit/40b74558771ba9db493728dcaabe43318daf9b97): `GODEBUG=asyncpreemptoff=1`.
- CL [201760](https://go-review.googlesource.com/c/go/+/201760), commit [`62e53b79227dafc6afcd92240c89acb8c0e1dd56`](https://github.com/golang/go/commit/62e53b79227dafc6afcd92240c89acb8c0e1dd56): signal preemption for `suspendG`.
- CL [201761](https://go-review.googlesource.com/c/go/+/201761), commit [`d16ec137568fb20e674a99c265e7c340c065dd69`](https://github.com/golang/go/commit/d16ec137568fb20e674a99c265e7c340c065dd69): conservative scanning at async safe points.
- CL [201762](https://go-review.googlesource.com/c/go/+/201762), commit [`177a36a5dc29854489825e8113ecb2cbb7070690`](https://github.com/golang/go/commit/177a36a5dc29854489825e8113ecb2cbb7070690): async scheduler preemption through `preemptone`.
- CL [201759](https://go-review.googlesource.com/c/go/+/201759), commit [`a3ffb0d9eb948409c0898c6b1803401c9bc68ed4`](https://github.com/golang/go/commit/a3ffb0d9eb948409c0898c6b1803401c9bc68ed4): x86 `asyncPreempt` register spill/restore.
- CL [207349](https://go-review.googlesource.com/c/go/+/207349), commit [`c3f149250e036f6bf77e7c9512dd3d57e1c78452`](https://github.com/golang/go/commit/c3f149250e036f6bf77e7c9512dd3d57e1c78452): mark compiler unsafe points.
- CL [230544](https://go-review.googlesource.com/c/go/+/230544), commit [`9d812cfa5cbb1f573d61c452c864072270526753`](https://github.com/golang/go/commit/9d812cfa5cbb1f573d61c452c864072270526753): retain stack maps only at calls and use conservative scanning for the interrupted frame.

[maintainer] The Go 1.14 release note summarizes the user-visible implementation change:

> Goroutines are now asynchronously preemptible. As a result, loops without function calls no longer potentially deadlock the scheduler or significantly delay garbage collection. This is supported on all platforms except `windows/arm`, `darwin/arm`, `js/wasm`, and `plan9/*`.

([Go 1.14 release notes](https://go.dev/doc/go1.14#runtime))

### 2.6 Recent changes

[implementation @go1.22+] CL [559798](https://go-review.googlesource.com/c/go/+/559798), commit [`a6a5c30d2b1338a8445de2499fbe7e9dda103efb`](https://github.com/golang/go/commit/a6a5c30d2b1338a8445de2499fbe7e9dda103efb), fixed wasm starvation between a “ping-pong” pair and the rest of the run queue by disabling `runnext` when there is no sysmon. The commit is candid about the remaining hole:

> Note that this CL doesn't do anything about single long-running
> goroutines. Without sysmon to preempt them, a single goroutine that
> fails to yield will starve the run queue indefinitely.

[implementation @go1.26.6] An arm64 correctness fix ensured the small frame created during injected async preemption is scanned, so a pointer in R30 is not missed: master CL [797521](https://go-review.googlesource.com/c/go/+/797521), commit [`a1298407792546b9e93393c903c26be9e87e8e3b`](https://github.com/golang/go/commit/a1298407792546b9e93393c903c26be9e87e8e3b); Go 1.26 backport CL [800360](https://go-review.googlesource.com/c/go/+/800360), commit [`cc312256f86bacb23f48c048c60c2694029c5643`](https://github.com/golang/go/commit/cc312256f86bacb23f48c048c60c2694029c5643). This repairs GC correctness at an async preemption; it does not add a language guarantee or a new scheduler safe-point class.

[implementation @go1.27] CL [740681](https://go-review.googlesource.com/c/go/+/740681), commit [`683aa8893a5e2e99ef48fa4502b507a0fe92acc8`](https://github.com/golang/go/commit/683aa8893a5e2e99ef48fa4502b507a0fe92acc8), conservatively scans extended/vector register state when an asynchronously preempted G is scanned. Again this is a correctness expansion for register contents, not a scheduler contract.

[implementation @go1.26.7] No relevant scheduling or preemption file changed between go1.26.6 and go1.26.7. The current envelope is therefore the one described above.

## 3. Fairness and eventual scheduling

### 3.1 Language guarantee

[synthesis] There is no language-level guarantee that a runnable goroutine eventually runs, no bounded-wait guarantee, and no real-time/deadline guarantee. A maximally portable semantic model must admit an execution in which one runnable goroutine is postponed forever, unless a particular library API supplies a narrower progress contract.

[maintainer] Russ Cox's 2009 answer in issue [#205](https://github.com/golang/go/issues/205#issuecomment-66048536) is unequivocal:

> It's true, the scheduler makes no attempt at fairness.
> I can't promise it ever will, but I'm sure it will get more
> complicated.
> If two tasks need to stay synchronized, they should arrange
> that explicitly via communication instead of relying on relative
> speeds of execution.

[maintainer] Ian Lance Taylor's 2014 answer is newer and framed as specification policy:

> It's quite difficult to specify scheduler behaviour in the absence of
> a happens-before relationship. I think the best we could do would be
> to say something like "the scheduler does its best to not starve any
> goroutine." I don't see how that would be a helpful statement.

([golang-nuts](https://groups.google.com/g/golang-nuts/c/PWt4r9b40bc))

[maintainer] The most useful modern intent/contract split appears in issue [#65178](https://github.com/golang/go/issues/65178). Michael Pratt wrote:

> Go does not have a real-time scheduler, or even a best-effort deadline-based scheduler, so it can theoretically have unbounded scheduling delay.

([comment](https://github.com/golang/go/issues/65178#issuecomment-1901203133))

[maintainer] Bryan Mills replied:

> I agree that the runtime is theoretically allowed to produce this behavior according to the language spec.
>
> However, the addition of non-cooperative preemption (#24543) set up a strong expectation that every runnable goroutine will _eventually_ be scheduled, and resolved a large number of previous scheduler fairness issues (linked from that proposal).
>
> We also explicitly made mutex locking starvation-free in #13086. To me, that suggests that this sort of goroutine starvation is not intended behavior.

([comment](https://github.com/golang/go/issues/65178#issuecomment-1901229934))

[synthesis] This is the cleanest answer to “promised or disclaimed?”: eventual scheduling is a strong gc-runtime expectation and starvation is treated as a bug, but the same maintainer agrees that the language specification allows it.

### 3.2 Official descriptive documentation

[maintainer] The FAQ describes current implementation goals, not a Go-spec contract:

> Setting it to 1 eliminates the possibility of true parallelism, forcing independent goroutines to take turns executing.

> Go’s goroutine scheduler does well at balancing goroutines and threads, and can even preempt execution of a goroutine to make sure others on the same thread are not starved. However, it is not perfect.

([Go FAQ, “How can I control the number of CPUs?”](https://go.dev/doc/faq#How_can_I_control_the_number_of_CPUs))

[synthesis] “Forcing … to take turns” should not be formalized as a universal fairness axiom: the next sentence is qualified (“does well,” “can,” “not perfect”), while primary maintainer statements say the spec allows unbounded delay.

### 3.3 gc's anti-starvation mechanisms

[implementation @go1.26.7] `findRunnable` draws from local/global queues, work stealing, timers, netpoll, and special runtime work ([`src/runtime/proc.go:3385-3388`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/proc.go#L3385-L3388)). It periodically checks the global run queue:

> Check the global runnable queue once in a while to ensure fairness.
> Otherwise two goroutines can completely occupy the local runqueue
> by constantly respawning each other.

[implementation @go1.26.7] The check is `pp.schedtick%61 == 0` ([`src/runtime/proc.go:3440-3449`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/proc.go#L3440-L3449)).

[implementation @go1.26.7] A `runnext` G shares the current G's timeslice. On ports without sysmon the runtime now refuses to use `runnext` “or risk starvation” ([`src/runtime/proc.go:7473-7488`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/proc.go#L7473-L7488)).

[implementation @go1.26.7] With the race detector, scheduling is deliberately randomized:

> To shake out latent assumptions about scheduling order,
> we introduce some randomness into scheduling decisions
> when running with the race detector.

([`src/runtime/proc.go:7462-7471`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/proc.go#L7462-L7471))

[maintainer] Pratt explained sysmon's role:

> sysmon preempts long-running goroutines, so without that preemption, the tight `stop.Load()` loop won't ever yield. That said, even with sysmon, the right combinations of goroutines should still theoretically be able to trigger long wait times.

([#65178 comment](https://github.com/golang/go/issues/65178#issuecomment-1904668477))

[maintainer] Austin Clements explained the `runnext`/sysmon interaction:

> What's supposed to be happening is that goroutines can switch off in runnext (the "hot slot") but they share a single time slice, and will get preempted for another goroutine if that time slice runs out. But sysmon is responsible for time slice preemption. You're right that without that, things can be arbitrarily unfair.

([#65178 comment](https://github.com/golang/go/issues/65178#issuecomment-1904703814))

[synthesis] These mechanisms make starvation unlikely and make many cases bugs in gc, but none constitutes a proof that every runnable G eventually executes. The source itself calls preemption best-effort.

### 3.4 Select fairness is not scheduler fairness

[normative] The only normative rule is “uniform pseudo-random selection” among communications that can proceed at that `select` execution; see §1.2.

[maintainer] In a 2015 golang-nuts discussion Rob Pike characterized that statistical rule as fair:

> It is fair. Starvation is only possible for finite time. As with any uniform statistical process, eventually it averages out.
>
> All other things being equal (which they never are, but ignore that), if multiple communications are ready in a select, the choice of which one proceeds is made by a fair pseudorandom coin toss.
>
> Starvation doesn't happen. Don't worry about it.

([golang-nuts, “SELECT statement: Is channel starvation possible?”](https://groups.google.com/g/golang-nuts/c/4BR2Sdb6Zzk))

[maintainer] Ian Lance Taylor described the intended engineering standard probabilistically:

> all that is necessary for the Go language and implementation is to make the probability of starvation due to unfortunate choices in select be a few orders of magnitude lower than the probability of program error due to hardware failure.

> I think that if you look at real numbers you will see that that is achieved when using a uniform pseudo-random choice.

(same [thread](https://groups.google.com/g/golang-nuts/c/4BR2Sdb6Zzk))

[synthesis] These statements concern repeated `select` choice under statistical assumptions. They do not promise that the goroutine executing the `select` is itself scheduled, and “probability 1” is not “all traces.” A demonic scheduler model should not infer trace fairness from them.

### 3.5 Narrow API-level progress clauses

[normative] `sync.RWMutex` contains a real, object-specific anti-starvation contract:

> If any goroutine calls RWMutex.Lock while the lock is already held by one or more readers, concurrent calls to RWMutex.RLock will block until the writer has acquired (and released) the lock, to ensure that the lock eventually becomes available to the writer.

([Go 1.26.7 `src/sync/rwmutex.go:22-25`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/sync/rwmutex.go#L22-L25))

[normative] `sync.Cond.Signal` expressly does **not** confer scheduling priority:

> Signal() does not affect goroutine scheduling priority; if other goroutines are attempting to lock c.L, they may be awoken before a "waiting" goroutine.

([Go 1.26.7 `src/sync/cond.go:80-81`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/sync/cond.go#L80-L81))

[synthesis] GoCore should model such object-local rules separately from scheduler fairness. “Lock eventually becomes available” constrains reader barging at that lock; it is not a statement that the writer goroutine receives CPU within any bound.

### 3.6 Channel waiter order is not a language guarantee

[maintainer] Issue [#11506](https://github.com/golang/go/issues/11506) documents that blocked operations could historically be delayed arbitrarily by “drive-by” goroutines. Russ Cox explicitly scoped the fix:

> I'm not talking about a language change, just a change to our implementation.

[maintainer] Rob Pike summarized the boundary:

> Language semantics require that the values be FIFO, but the implications of that with multiple goroutines reading the values are unspecified and muddy at best.

([comment](https://github.com/golang/go/issues/11506#issuecomment-117860086))

[maintainer] Austin Clements wrote:

> From a specification perspective, it's true that our current approach satisfies the happens-before graph, but it does _not_ satisfy liveness. That's a formally defined, reasonable, and desirable property we could specify as a requirement of channels without specifying something as specific as FIFO blocking.

[maintainer] He cautioned:

> This seems like the exact same mistake as making map order deterministic or goroutine scheduling deterministic. People can and will come to depend on this and eventually we may want to weaken it.

([comment](https://github.com/golang/go/issues/11506#issuecomment-117882014))

[maintainer] Rick Hudson's conclusion was:

> I believe we can build fairness on top of weaker unfair semantics so not cooking the stronger semantics into Go is the way forward.

([comment](https://github.com/golang/go/issues/11506#issuecomment-118027081))

[implementation @go1.26.7] The current channel `waitq` is linked FIFO in the runtime ([`src/runtime/chan.go:872-918`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/chan.go#L872-L918)), but this is implementation fact, not portable semantics.

## 4. The busy-wait wedge

### 4.1 Racy ordinary-memory polling

[normative] The memory model gives almost exactly this example:

```go
var a string
var done bool

func setup() {
	a = "hello, world"
	done = true
}

func main() {
	go setup()
	for !done {
	}
	print(a)
}
```

[normative] It concludes:

> Worse, there is no guarantee that the write to `done` will ever be observed by `main`, since there are no synchronization events between the two threads. The loop in `main` is not guaranteed to finish.

> In all these examples, the solution is the same: use explicit synchronization.

(Go memory model, §"Incorrect synchronization" — mem#badsync at the pin; live: https://go.dev/ref/mem, anchor `incorrect`)

[synthesis] This example alone defeats any claim that an ordinary racy spin is guaranteed to complete. Its stated reason is memory observation, so it does not by itself settle a race-free atomic spin; scheduler evidence does.

### 4.2 Atomic or otherwise race-free polling

[maintainer] The pre-Go-1.14 issue [#10958](https://github.com/golang/go/issues/10958) states:

> Currently goroutines are only preemptible at function call points. Hence, it's possible to write a tight loop (e.g., a numerical kernel or a spin on an atomic) with no calls or allocation that arbitrarily delays preemption.

[maintainer] The async-preemption design says the extreme failure directly:

> In really extreme cases, it can cause a program to halt, such as
> when a goroutine spinning on an atomic load starves out the
> goroutine responsible for setting that atomic.

([proposal lines 79–92](https://github.com/golang/proposal/blob/0be13090fdb0cbae0d71641bb676d924bc1c94de/design/24543-non-cooperative-preemption.md#L79-L92))

[maintainer] Austin Clements later found the same pattern in production after inlining removed cooperative points:

> We recently started inlining the fast-paths of sync.RWMutex.RLock and RUnlock, which means the fast path of this loop can execute without preemption points. If that causes the goroutine that should be setting c.flushed to not run, then this leads to a deadlock.

> Obviously this busy loop isn't great, but it's interesting because it was in production code, and only started to fail when both RLock and RUnlock were inlined, the RWMutex was uncontended (otherwise it falls back to the slow path, which has a preemption point), and the goroutine schedule led to the goroutine that was supposed to set flushed getting blocked behind the spinning goroutine.

([#24543 comment](https://github.com/golang/go/issues/24543#issuecomment-521751343))

[maintainer] Async preemption was intended to hide this implementation hazard. Clements wrote:

> This ought to be invisible beyond eliminating bizarre deadlocks and improving throughput in some cases. If it's not invisible, we'd love to know why and better understand that.

([#24543 comment](https://github.com/golang/go/issues/24543#issuecomment-543289991))

[synthesis] Intent and contract diverge. On mainstream gc go1.26.7 ports, an ordinary user-Go atomic spin is normally async-preemptible and the setter/sender is expected eventually to run. But a conforming program may not use that observation as a portable termination proof: the language allows starvation; wasm/Plan 9 lack async preemption; it can be disabled; and unsafe/runtime/assembly/secret regions remain non-async-preemptible.

### 4.3 If “another wants to send it a value” means a channel

[normative] A blocked sender's operation cannot complete until the channel rules permit it. Nothing in the channel rules requires a spinning receiver goroutine to be scheduled, to execute a receive, or to execute it before any bound. If the spinner polls `len(ch)`, the specification also does not turn `len` into synchronization or a yield point.

[maintainer] For competing sends or receives, Ian Lance Taylor's answer is directly portable:

> The answer to that question is that there are no guarantees. The goroutine scheduler is not described in the language spec. Different implementations may act differently.

([golang-nuts](https://groups.google.com/g/golang-nuts/c/PWt4r9b40bc))

[implementation @go1.26.7] If the sender actually blocks in `chansend`, gc parks it ([`chan.go:257-283`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/chan.go#L257-L283)). If the send completes and wakes a blocked receiver, it calls `goready` but keeps executing ([`chan.go:312-350`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/chan.go#L312-L350)). Neither path supplies a normative scheduling order.

[synthesis] Recommended verdict for the measured wedge: **gc-completes is implementation evidence, not a conforming-program assumption**. The portable model should include the completing execution and an unfair execution in which the needed goroutine is never selected.

## 5. Memory-model rewrite discussions #47141 and #56010

### 5.1 Discussion #47141

[maintainer] [Discussion #47141, “Updating the Go memory model”](https://github.com/golang/go/discussions/47141), was opened by Russ Cox on 2021-07-12 and contains 15 top-level comments and 51 replies. Its stated purpose was feedback on the memory-model update:

> I posted a blog post Updating the Go memory model about some changes I am planning to propose regarding Go's memory model. This discussion is for collecting feedback about those changes before filing an official proposal.

[synthesis] I audited the complete rendered thread, including replies, for `schedul`, `preempt`, `starv`, `liveness`, `eventually`, `progress`, `yield`, `spin`, and busy-wait variants. There is no scheduling, preemption, fairness, starvation, or progress guarantee discussion. The only `fair` match is Russ Cox saying “Fair enough” about adding bitwise atomic operations. Channel discussion is about happens-before ordering, not whether a goroutine eventually executes.

[synthesis] Therefore #47141 provides no affirmative evidence for scheduler fairness and no “programs may not assume scheduling” statement. Its important negative result is scope: the 2022 rewrite formalized memory-operation executions and synchronization, not execution progress.

### 5.2 Discussion #56010

[maintainer] The supplied entry point is not a second memory-model thread. [Discussion #56010](https://github.com/golang/go/discussions/56010) is titled **“redefining for loop variable semantics”**, opened 2022-10-03, with 50 comments and 241 replies. The opening says:

> We have been looking at what to do about the for loop variable problem (#20733), gathering data about what a change would mean and how we might deploy it.

[synthesis] I audited the complete rendered thread for the same terms. There is no scheduler/preemption/fairness/liveness guarantee discussion. Goroutines appear only as examples of closures capturing loop variables. Matches for `fair` are ordinary English (“A fair point”), not fairness semantics.

[synthesis] #56010 contributes no scheduler evidence. Treating it as memory-model or scheduler authority would be a citation error.

## 6. Prior formalizations and the envelopes they chose

### 6.1 MiGo / “Fencing off Go”

[secondary] Lange, Ng, Toninho, and Yoshida, *Fencing off Go: Liveness and Safety for Channel-Based Programming*, POPL 2017, formalizes the message-passing fragment as MiGo ([DOI 10.1145/3009837.3009847](https://doi.org/10.1145/3009837.3009847); [extended paper](https://arxiv.org/abs/1610.08843)). It states:

> The justification for the liveness of t0 is that the internal choice always has the potential to enable the output on y (assuming a fairness condition on scheduling).

([extended paper PDF](https://web.tecnico.ulisboa.pt/bernardo.toninho/papers/popl17-go.pdf), §1.1, PDF p.2)

[secondary] The same paper says its calculus “mirrors very closely the intended semantics of the channel-based Go constructs,” but the quoted fairness condition is an analysis assumption; it is not justified there by the Go specification or runtime-maintainer sources. MiGo therefore narrows the conforming scheduler envelope for its liveness result.

### 6.2 Gomela / Promela and Spin

[secondary] Lange, Ng, Toninho, and Yoshida, *Bounded verification of message-passing concurrency in Go using Promela and Spin* ([arXiv:2004.01323](https://arxiv.org/abs/2004.01323)), extracts bounded Promela models of the message-passing fragment. Its evaluation states:

> Because if-then-else statements are translated to non-deterministic choices, our approach is unable to determine that the two conditional blocks are “synchronised” by the same invocation of function f().

([paper, §4](https://arxiv.org/abs/2004.01323))

[secondary] More scheduler-relevantly, it describes examples with “a non-terminating for-loop” paired with a waiting goroutine and treats them as partial-deadlock/termination-analysis cases. The model abstracts communication control and explores nondeterminism; the paper does not derive a scheduler-fairness premise from Go's normative sources. It is not a faithful gc timeslice/preemption model.

### 6.3 Goose / Perennial

[secondary] Goose translates a subset of Go to Perennial's Coq/Rocq language; it does not claim arbitrary-Go coverage ([Perennial README at commit `43d4efabc22eb148eb239ebee89d1dd2ee54c900`](https://github.com/mit-pdos/perennial/tree/43d4efabc22eb148eb239ebee89d1dd2ee54c900)).

[secondary] Its generic concurrent language step chooses any expression `e1` appearing in a decomposition `t1 ++ e1 :: t2` and replaces it with its primitive-step result plus forked expressions ([`src/program_logic/language.v:118-132`](https://github.com/mit-pdos/perennial/blob/43d4efabc22eb148eb239ebee89d1dd2ee54c900/src/program_logic/language.v#L118-L132)). `Fork e` returns the unit value and appends `e` as a new thread ([`src/goose_lang/lang.v:1332-1345`](https://github.com/mit-pdos/perennial/blob/43d4efabc22eb148eb239ebee89d1dd2ee54c900/src/goose_lang/lang.v#L1332-L1345)). No fairness condition occurs in this transition relation.

[synthesis] That is the broad envelope suitable for safety/partial-correctness reasoning: arbitrary finite interleavings, with unfair infinite executions not excluded by the step relation. The inspected source does not justify this choice from gc behavior; it is the underlying Iris-style concurrency model.

### 6.4 Gobra

[secondary] Gobra is a verifier for a large Go subset, including goroutines and channels, but its default theorem shape does not require global progress. Its tutorial says exactly:

> By default, Gobra proves partial correctness, i.e., if a function terminates then its postcondition holds.

([Gobra tutorial at commit `810de065be64d2bfbf85fa6aed48f4be642e34bb`](https://github.com/viperproject/gobra/blob/810de065be64d2bfbf85fa6aed48f4be642e34bb/docs/tutorial.md#L196-L200))

[secondary] Termination can be requested through explicit decreases measures, but this is program proof machinery, not a formalization of gc scheduler fairness. Gobra therefore largely avoids needing to pick a global eventual-scheduling guarantee for its default partial-correctness results.

### 6.5 K-Go

[secondary] Zhao et al., *K-Go: An executable formal semantics of Go language in K framework* (2023), describes goroutine and channel rules but says: “Because this article describes static semantics, dynamic content analysis of goroutine scheduling is ignored here.” ([DOI 10.1049/blc2.12024](https://doi.org/10.1049/blc2.12024)). It is not evidence for a scheduler envelope.

### 6.6 GoL / Godel2

[secondary] Gabet and Yoshida, *Static Race Detection and Mutex Safety and Liveness for Go Programs*, ECOOP 2020, gives a nondeterministic reduction semantics for a Go subset and checks lock/channel liveness ([DOI 10.4230/LIPIcs.ECOOP.2020.4](https://doi.org/10.4230/LIPIcs.ECOOP.2020.4); [extended paper](https://arxiv.org/abs/2004.12859)). Its prose says:

> Lock liveness identifies the ability of (read-)lock requests to always eventually fire.

[secondary] The paper defines its reachability notation:

> We write P ⇓o if P −→∗P′ and P′ ↓o.

[secondary] Its formal liveness definition then uses that existential reachability:

> Program P is live if for all P such that P −→∗(ν˜u)P, if P ↓l⟨l⟩ or P ↓rl⟨l⟩ then P ⇓τl.

([extended paper PDF, §3.1, Definitions 5 and 7, PDF p.8](https://mrg.cs.ox.ac.uk/publications/static-race-detection-and-mutex-safety-and-liveness-for-go-programs/full.pdf))

[secondary] The channel extension analogously says:

> Channel Liveness: no channel action blocks indefinitely, ie. all channel actions lead to synchronisation on the channel eventually (or on a channel of the list of guarding actions for a select construct that has no silent action guard).

[secondary] It formalizes that conclusion with `P ⇓τc`/`P ⇓τci` ([published paper PDF, §7.2, Definition 34, PDF p.22](https://drops.dagstuhl.de/storage/00lipics/lipics-vol166-ecoop2020/LIPIcs.ECOOP.2020.4/LIPIcs.ECOOP.2020.4.pdf)).

[synthesis] This is may-reachability from every reachable state, not a claim that every infinite scheduler trace eventually takes the enabled reduction. The paper cites the Go memory model for happens-before, but does not derive a scheduler-fairness rule from Go normative text. It is another useful warning that a formalization's term “liveness” need not mean fair eventual scheduling.

### 6.7 Assessment

[synthesis] The surveyed formalizations fall into four camps:

1. Add fairness explicitly to obtain liveness (MiGo).
2. Use arbitrary nondeterministic interleaving for safety/partial correctness (Goose/Perennial; bounded Promela exploration).
3. Define liveness as availability of a future reduction, without asserting fair execution of all traces (GoL/Godel2).
4. Avoid scheduler liveness through partial-correctness theorem shapes or omit dynamic scheduling (Gobra; K-Go).

[synthesis] None of the surveyed work derives a fair scheduler from the Go specification. MiGo's fairness premise is the clearest example of an extra-model assumption; Goose's unconstrained thread choice is closest to the conforming-language envelope supported by the primary sources in this dossier.

## 7. Treasure watch

### 7.1 Surprising documented guarantees and non-guarantees

[normative] The `select` distribution really is specified as uniform pseudo-random, even though runnable-G choice is unspecified. A model that represents both with the same unweighted nondeterministic oracle loses a normative distinction.

[normative] `sync.RWMutex` promises writer anti-barging (“eventually becomes available”), while `sync.Cond.Signal` explicitly disclaims scheduling priority. These are narrower than scheduler fairness but should not be erased if GoCore models these APIs.

[normative] The memory model's goroutine-creation example says “will print … at some point in the future.” This is the one liveness-sounding normative example, but it conflicts with treating the formal memory model as a progress logic. Preserve it as an ambiguity/illustrative sentence, not a silently assumed strong-fairness axiom.

[implementation @go1.26.7] `GOEXPERIMENT=RuntimeSecret` introduces an explicit async-nonpreemptible region to avoid copying confidential register/stack material. This is a new example of why “async preemptible at every user instruction” is false even on a supported OS.

[implementation @go1.26.7] The 10 ms constant is commonly repeated as a timeslice guarantee; source comments calling the request “purely best-effort” contradict that folklore.

[implementation @go1.26.7] The runtime deliberately randomizes scheduling under `-race` to expose tests that depend on scheduling order. This is implementation policy evidence that stable observed order is not intended as contract.

### 7.2 Open issues/proposals worth watching

[maintainer] Issue [#71134](https://github.com/golang/go/issues/71134), **“runtime: async preemption (or alternative) for wasm,”** remains open. Its body says:

> Due to its single-threaded nature, js/wasm have no sysmon thread, and thus no asynchronous preemption. Thus the pitfalls of Go prior to asynchronous preemption apply: tight loops that fail to yield may delay scheduling indefinitely.

[maintainer] It also notes: “Plan9 is also missing async preemption, but that simply needs an implementation.”

[secondary] A third-party proposal on the Go issue tracker, issue [#51071](https://github.com/golang/go/issues/51071), **“runtime: investigate possible Go scheduler improvements inspired by Linux Kernel's CFS,”** remains open. It proposes scheduler policy/priority changes, not a language-semantics change, and has no accepted design as of the cutoff.

[implementation @go1.26.7] Issue [#72031](https://github.com/golang/go/issues/72031) is referenced directly in `isAsyncSafePoint`: runtime/internal-runtime/reflect checks remain because compiler unsafe-point markings have not made the runtime checks removable ([`preempt.go:463-478`](https://github.com/golang/go/blob/e3336a22ad3f0a90bd252c95d8b5544e02674205/src/runtime/preempt.go#L463-L478)).

[secondary] A 2026 third-party proposal on the Go issue tracker, issue [#78189](https://github.com/golang/go/issues/78189), would add cooperative `Preempt()` checks for registered JIT/user frames at loop back-edges or function entries. It is open and unaccepted; it illustrates that foreign/generated frames remain a live safe-point design boundary, not a current guarantee.

## Final synthesis: what a conforming program may assume

[synthesis] The statements in this section are **this dossier's synthesis**, not quotations from the Go project.

[synthesis] A conforming Go program may assume:

- Each goroutine's executed operations respect that goroutine's specified sequential control flow and expression-evaluation rules.
- A `go` statement creates an independent goroutine and establishes the memory-model synchronized-before edge from the `go` statement to the child's start, if/when that start occurs.
- Channel operations have the specified readiness, blocking, FIFO-value, close, and happens-before behavior.
- At a `select` evaluation with multiple communications that can proceed, one is chosen by the specified uniform pseudo-random selection.
- `runtime.Gosched` yields the processor and leaves the caller runnable; it does not promise a particular successor or bounded resumption.
- `runtime.GOMAXPROCS` bounds simultaneous execution; `runtime.LockOSThread` constrains OS-thread placement; neither supplies order, priority, or progress.
- `runtime.Goexit` in the main goroutine has its documented program-lifetime behavior, distinct from `main` returning.
- Narrow standard-library progress/priority clauses, such as `RWMutex` writer anti-barging and `Cond.Signal`'s priority disclaimer, apply to those APIs.

[synthesis] A conforming Go program may **not** assume:

- that a switch can occur only at function calls, loop back-edges, channel operations, allocations, syscalls, or any other source-level list;
- that function calls or every channel operation force a switch;
- that a running goroutine has a fixed or maximum timeslice;
- that a runnable goroutine is eventually scheduled, either at all or within a bound;
- that `GOMAXPROCS=1` supplies round-robin or fair scheduling;
- that a goroutine made runnable by a send, receive, timer, unlock, or `goready` runs next;
- that blocked senders/receivers or lock waiters are served FIFO unless a particular API explicitly promises the relevant ordering;
- that repeated `select` executions give deterministic round-robin fairness or that a case wins on every possible infinite trace;
- that observed gc behavior—especially completion of a tight atomic busy-wait—is portable to other implementations, ports, `GODEBUG` settings, or future releases;
- that the 10 ms gc preemption threshold is a deadline or upper bound.

[synthesis] Recommended GoCore scheduler envelope:

1. **Portable language layer:** arbitrary nondeterministic interleaving at instruction/semantic-step granularity, with no forbidden switch points derived from source syntax and no fairness premise. Permit infinite stuttering/starvation traces. Enforce only the language's operation-level blocking/readiness, happens-before, FIFO-value, and `select`-choice constraints.
2. **Library layer:** add only documented per-primitive rules (`Gosched`, `RWMutex`, `Cond`, etc.), without promoting them to global scheduler fairness.
3. **gc go1.26.7 refinement:** optionally model blocked, synchronous-prologue, and async safe points; platform/configuration exclusions; sysmon's 10 ms request threshold; global-queue `%61` polling; `runnext` timeslice inheritance; and best-effort failed preemption. Mark every such rule `[implementation @go1.26.7]` so no theorem over the portable layer accidentally depends on it.
4. **Liveness proofs:** if a theorem needs weak or strong fairness, state it as an explicit environmental/model assumption. Do not present it as Go conformance. A useful theorem split is “safety for all conforming schedules” versus “termination/liveness under fairness assumption F.”

[synthesis] Bottom line: **Go intends practical forward progress and gc aggressively works to provide it, but the language contract does not promise eventual scheduling.** The sound nondeterministic envelope for a conforming implementation is therefore wider than gc's observed scheduler and must admit starvation.
