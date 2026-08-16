# Overrides: library code the machine does not model (2026-08-16)

Design note, written in the post-autonomy audit round of the gallery
campaign, recording a discussion and a user ruling rather than
chartering work. Nothing here is scheduled. The occasion is extension
**E5** (`docs/gallery-campaign-log/g2.md` §E5), which gave the frontend
its first stdlib shim — a Go-source `strings.Fields` injected into the
user's package before type-check — and immediately raised the question
the north-star target will ask in earnest: *what do we do about library
code we are not going to model?*

**The user's ruling, verbatim:**

> "fine, but the injection mechanism is a bit of a wart and should be
> retired as soon as we see another instance."

So E5 stands, and it stands **as a recorded wart with a retirement
trigger**. The rest of this note separates the three things that get
confused whenever "overrides" is said, because they have different trust
consequences: how the machine EXECUTES library code, how a PROOF gets
past a call it does not want to step through, and what either of those
does to the trust story.

---

## Layer 1 — execution: how the machine runs library code

**What E5 does today.** The frontend scans for an allowlisted call shape
(`strings.Fields(x)`, the allowlist's one entry), and when it is
present, parses a Go-SOURCE shim in as a synthetic file before
type-checking, rewriting exactly those call sites into ordinary static
calls to the injected function. The shim then lowers through the
ordinary pipeline; the consumer's golden pin records its lowered body
verbatim. No GoCore change, no wire change, no decoder change — the
whole mechanism is quarantine-zone lowering code.

**Why it is a wart.** The mechanism is source injection: it edits the
user's package before type-check, which means the thing the type-checker
sees is not the thing the user wrote. It is deterministic and
collision-checked (reserved shim names refuse loudly rather than
silently merging), and at ONE allowlist entry it is legible. At five it
would be a small compiler pass nobody designed, with the injected text
as its only specification.

**RETIREMENT TRIGGER — the second shim instance.** The moment a second
library function needs shimming, the injection mechanism is retired in
favour of a **linked registry**:

* the library functions are **pre-lowered once** into a Func library —
  the same `Func` values the frontend emits for user code, produced by
  the same pipeline from the same Go source;
* the frontend **links** a call to a registered library function to the
  corresponding `FuncId`, exactly as it links a call to a user function;
* the machine sees **ordinary `Func`s** and does not know a registry
  exists.

That is the same trust position with none of the source surgery: the
shims stay Go source in the modeled subset, the registry replaces "paste
it into the user's package" with "resolve the name", and the golden pins
keep recording the lowered bodies. The second instance is the trigger
because that is when the injection pass stops being one legible special
case and starts being an unspecified compiler.

**THE TCB CONSTRAINT, and it is the whole point of this section.** The
registry lives **at the frontend boundary and NOWHERE else**. It must
never become a machine mechanism — no override table consulted by
`stepFn`, no "if this FuncId is a library function, do this instead".

The reason is not taste. An override table inside the machine would put
library specifications inside the TRUSTED semantic core: the interpreter
is the model of Go and the statement language both, so anything it
consults is something every theorem's meaning depends on. Worse, every
top-level statement would have to quantify over the table — "for every
override environment, the run returns…" — or silently fix one, which is
the same failure wearing a different hat. Today a headline says *this
program, run on the machine, returns this*. With an in-machine override
table it would say *this program, run on the machine CONFIGURED THIS
WAY, returns this*, and the configuration would be an unaudited input to
every claim in the gallery. The frontend boundary is where
frontend-specific concerns already live and fail closed; a registry
there is one more piece of lowering, and the machine's story is
unchanged.

---

## Layer 2 — reasoning: getting past a call without stepping through it

A different problem with the same word attached. Even when the machine
CAN run the callee, a proof usually should not want to: stepping a
library call open re-derives the callee's behaviour at every call site,
which is the cost that makes big targets impossible.

The mechanism that fits our architecture is a **proof-side call-span
combinator**: given the callee's own theorem — its body's behaviour at
an abstract heap, allocation frontier, return continuation and caller
environment — produce the caller-side span across the call, as the
composition `enterFrame → body → return_frame`, with the conditioned
facts as hypotheses. This is R5's **P-H** (`docs/2026-08-16_wp-library-design.md`,
"Call spans / recursion packs"): the entry half exists in the kit
(`StepKit.stepFn_call_enter`), the exit half (`stepFn_return_frame`) is
re-derived per example today, and the combinator itself is unbuilt with
two landed consumers waiting (fibmemo and stein, whose copies differ
only in the callee facts).

Three properties matter here:

1. **It is an UNTRUSTED METHOD.** It consumes a callee theorem and
   produces a caller theorem; if it is wrong, the proof fails to
   elaborate. Nothing about it enters a statement, and no headline's
   closure grows by a name.
2. **It is the compositional mechanism the raft target actually needs.**
   A target of that size is a call graph, and proving it means consuming
   callee theorems rather than re-walking callee bodies.
3. **It composes with layer 1 rather than competing with it.** If the
   callee is a registered library function, its theorem is proven once
   about the library's `Func` and reused at every call site — which is
   what makes the registry worth having beyond tidiness.

**The SAW correspondence, named** (from the SAW literature — there is no
`deps/saw` checkout in this repo to cite line-for-line, so treat the
mechanism sketch as reconstructed and check it against SAW's manual
before building on the analogy). SAW's `crucible_llvm_verify` takes a
list of *overrides*: previously proven specifications that are applied
at matching call sites instead of symbolically executing the callee, and
each override is itself discharged as a proof obligation. That is
exactly layer 2 — a proof-side device, checked, not trusted — and the
name is worth keeping because it is the established one. What SAW calls
an override is what this note calls a call-span with a callee theorem;
what E5 does is NOT that, and calling both "overrides" is the confusion
this note exists to prevent.

---

## Layer 3 — the trust story, which is a testing story

For library code the machine does not model, the honest framing is the
one every test suite already uses: **the machine runs a mock; the oracle
runs the real library.**

* the machine executes the shim (a Go-source model of `strings.Fields`);
* `go run` executes the REAL `strings.Fields`;
* therefore **every differential row whose control flow crosses a
  shimmed call is a direct oracle test of the mock's fidelity** — any
  semantic daylight shows up as a values-level mismatch on that row;
* and for a pure deterministic function the envelope is a single
  behaviour per input, so the rows bite unusually hard: one row per
  behaviour class pins that class outright.

E5's evidence is the pattern to repeat: 8 `strings/fields-conformance`
rows chosen by behaviour class (leading/trailing/consecutive whitespace,
NBSP/NEL/EM-SPACE/IDEOGRAPHIC-SPACE splitting, the U+200B non-split,
invalid UTF-8), 14 consumer rows re-crossing the shim on every built
input, and a 600,000-trial shim-vs-stdlib fuzz with zero mismatches.

**This story is unchanged by registry-vs-paste.** Whether the shim is
injected as source or linked from a pre-lowered registry, the machine
runs the mock and the oracle runs the real thing, and the corpus plus
the fuzz is what argues the mock is faithful. That is precisely why the
retirement trigger is a hygiene decision rather than a trust decision:
nothing in this section moves when it fires.

**What the story does NOT cover, said plainly.** Mock fidelity is a
LOWER bound argument of the usual kind: the rows witness agreement on
what they exercise. A shim for a function with real latitude (map
iteration, allocation, anything scheduler-visible) would need the
envelope argued from the spec text the way every other latitude point
is, and the corpus could not settle it. `strings.Fields` is pure and
deterministic, which is why one allowlist entry was a defensible place
to start and why widening the allowlist owes a fresh argument per
function.

---

## Summary

| layer | mechanism | where it lives | trust status |
|---|---|---|---|
| execution | Go-source shim, injected today, LINKED REGISTRY after the second instance | frontend boundary, never the machine | in the lowering's trust surface; golden-pinned, differentially tested |
| reasoning | call-span combinator consuming callee theorems (R5 §P-H); SAW's "overrides" | proof layer | untrusted method — wrong means it fails to elaborate |
| trust | mock-vs-real: machine runs the shim, oracle runs the library | the differential corpus + fuzz | lower-bound argument; unchanged by registry-vs-paste |

Open, and deliberately not decided here: when the second shim instance
arrives (that is the trigger, not a date), what the registry's
pre-lowering step looks like in `tools/nativefrontend` and whether the
library Funcs get their own golden pins as a set; and whether the
call-span combinator is built at its two current consumers or waits for
the raft-scale consumer that makes it urgent.
