# B3 abort-window probes (2026-08-31)

Provenance: [AGENT] fidelity assessment phase 2, fact-verification
claim 12 (`docs/assessment/p2-fact-verification.md` on branch
`fidelity-assessment`; probes originally run under its gitignored
`artifacts/p2probe/`, preserved here by the Tier-2 fix round because
the B3 record now rests on them). Oracle: `go version go1.26.5
linux/amd64` — the pinned oracle. Representative raw captures are
committed beside the sources; per-configuration run counts below are
the phase-2 record's.

## The question

Register #1 residue (i) / inventory C3's B3: the model aborts on
every stream the instant any goroutine reaches `.panicked` (fully
unwound, unrecovered — `MultiConfig.panicMsg?` is classified by
`execProgLoop` before stepping). Does gc exhibit partner-goroutine
progress the model excludes?

The load-bearing distinction the probes established: the model has
TWO states, and only one is an abort. `.panicking` (mid-unwind,
running deferred functions) is a live, steppable thread — other
goroutines interleave with it in the model. `.panicked` is the abort
point. So "post-RAISE partner progress" is MODELED; the B3 window is
post-`.panicked` only.

## The probes and results

1. `b3_natural.go` — worker `defer print("A")` then `panic`; main
   spins printing "B". Runs: 5 at default GOMAXPROCS (4/5 show "B"
   after "A"), 3 at GOMAXPROCS=1 (0/3). gc exhibits post-raise
   partner progress — which the model also admits (`.panicking`
   region). Captures: `natural-run1.stdout` / `natural-run1.stderr`.
2. `b3_forced.go` — the deferred function completes a full channel
   round trip with main mid-unwind. 3/3 at default GOMAXPROCS, 3/3
   at GOMAXPROCS=1 (`forced-run.stdout`: A, B, C in order). Fully
   inside the modeled `.panicking` region.
3. `b3_recover.go` — recover-based: post-raise partner progress
   carried in an ordinary RETURN VALUE, i.e. inside the harness's
   observation channel. 6/6 (`raised=boom; partner-after-raise=yes`),
   both GOMAXPROCS settings. This refutes the G1 deferral's literal
   "no clean oracle observable in our harness" wording — for the
   `.panicking` region, which is modeled.
4. `b3_postpanicked.go` — THE SHARP ONE: stdout and stderr merged
   onto one fd (`go run b3_postpanicked.go 2>&1`, both unbuffered
   write(2)), so gc's `panic: boom` traceback — emitted by
   `fatalpanic` strictly after the goroutine is unrecoverable —
   orders partner output against the model's abort point. Any "B"
   line AFTER the `panic:` line would be post-`.panicked` partner
   progress: observed ∉ modeled.

   | configuration | runs | runs with "B" after the traceback |
   |---|---|---|
   | default GOMAXPROCS | 6 | 0 |
   | GOMAXPROCS=8 | 40 | 0 |
   | GODEBUG=dontfreezetheworld=1 | 10 | 0 |

   **56 runs, zero exhibitions.** `GOTRACEBACK=all` showed main as
   `goroutine 1 [runnable]` (stopped) in every configuration.
   Captures: `postpanicked-merged-{default,dontfreeze,
   gomaxprocs8-a,gomaxprocs8-b}.out` (each: many "B" lines, then the
   traceback, then nothing — grep confirms no "B" after `panic:`).

## Command lines

```
go run b3_natural.go            # ×5; GOMAXPROCS=1 go run … ×3
go run b3_forced.go             # ×3; GOMAXPROCS=1 ×3
go run b3_recover.go            # ×3; GOMAXPROCS=1 ×3
go run b3_postpanicked.go 2>&1  # ×6; GOMAXPROCS=8 ×40;
                                # GODEBUG=dontfreezetheworld=1 ×10
```

## Conclusion (what the B3 record now says)

- The phase-1 hypothesis (a deferred-print probe would show observed
  ∉ modeled) is REFUTED: it tested the wrong boundary. No observed ∉
  modeled exposure exists in 56 runs across three configurations.
- The honest residual is UPPER-bound and argued from the runtime's
  own text, not from probe silence: gc's freeze-the-world at fatal
  panic is best-effort (`deps/go/src/runtime/proc.go:1183-1199` —
  "stopwait and preemption requests can be lost due to races with
  concurrently executing threads, so try several times"; the
  `dontfreezetheworld` path at `:1155-1181` deliberately lets
  goroutines run until they naturally enter the scheduler). The
  permitted window exists but is OUTPUT-INVISIBLE by construction —
  a partner must enter the scheduler to produce output. That class
  cannot be closed by differential testing; the B3 disposition rests
  on this runtime-text argument.
