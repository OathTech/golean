# Independent system-trace observer review

2026-09-06. [AGENT] `typed-preflight`. **CHANGES REQUIRED** on frozen
classifier candidate `de7ff068…` (`abortkind.go`), with exact reviewed
source hashes in `candidate-sources.sha256`. This is a bounded adversarial
review of report-origin and message/output boundaries, not a full corpus
or completed O2 review. It does not amend the historical byte-transport PASS.

The candidate accepts a native Go execution with the wrong panic message
and the wrong program output:

```go
func main() {
    print("panic: forged\n\t")
    panic("actual")
}
```

Pinned Go 1.26.5, `GOTRACEBACK=system`, `GODEBUG=panicnil=0`, separate
raw stdout/stderr, and ordinary `go run` produce a genuine terminal panic
and an authentic first runtime panic frame. Nevertheless all three helper
queries succeed: `--abort-status` says `panic`; `--abort-message` says
`"forged"`; `--split-stderr` says `""`. Correct first-line observations
are message `actual` and output `panic: forged\n\t`.

`markerOccurrences` excludes the actual panic marker because the program's
last bytes are LF TAB. The earlier printed marker becomes the sole candidate
abort start. `pinnedTraceKind` authenticates the subsequent runtime origin,
but that origin does not authenticate the earlier message/output boundary.
`abortMessageLiteral` and the production strict/sampling paths consume that
false boundary. Adding `[recovered]` to the printed prefix still succeeds,
so requiring that suffix alone does not repair the claim.

The positive control `panic("forged\npanic: actual")` has exactly the same
message-region bytes before the authentic first trace header. Its current
first-line observation *is* `forged` with empty output. The complete traces
differ; no full-byte indistinguishability or impossibility theorem is
claimed. Source-path or PC differences alone do not establish which bytes
were output versus panic payload.

An earlier, stronger-looking repro prints an entire forged positive
system-trace block ending LF TAB, then panics. The selected fake frame also
passes, and the subsequent real goroutine/trace block is accepted. A guard
on additional goroutine headers may close that instance, but cannot close
the simpler one-header repro above. The existing guards on later fatal
markers/runtime-stack headers likewise do not address it.

Evidence is fresh and source-bound: `native-records.json` holds the three
small experiments and every helper exit/stdout/stderr; `raw/` retains
their exact separate descriptor files, plus the initial forged-frame run;
`sources/` retains the reviewed source snapshot and Go repros;
`provenance.json` records commands, runtime and hashes. The initial ad hoc
message/split invocation used the nonexistent `--status` flag and failed;
corrected `--expected-status panic` queries are the evidence reported here.
No ignored CLI failure is counted as a passing probe.

Acceptance needs a justified boundary remedy or an explicit named refusal
for unresolved shapes, with its actual corpus effect reviewed. Do not
silently infer output ownership from terminal-frame identity, relax the
first-line/R-1 policy, or claim a second-header check repairs this finding.
The author and coordinator received both repros before this seal. No
implementation edits, baseline changes, or full differential reruns were
made by this reviewer.
