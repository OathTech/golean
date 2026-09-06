# Independent diagnostic observer implementation review

[AGENT] `typed-preflight`, 2026-09-06 UTC. **Bounded PASS** for the frozen
diagnostic source manifest SHA256
`21b9d359558e74e873e624a744ba95ba22b9cd1b42600186c6c76a63e11d1d9a`
in `typed-observer-controls`. This verdict covers the three diagnostic
oracle paths, their dedicated controls and ordinary-CI wiring. It does not
claim a fresh full diagnostic census or Go-versus-model conformance.

`candidate-sources.json` identifies all 16 frozen inputs. `source.tar.gz`
retains them and the complete helper source. Every candidate hash was
checked before and after the fresh probes. The shared helper is byte-equal
to the separately reviewed production candidate (`1bd2022b`); the author's
temporary borrowing must be replaced by integration of its reviewed commit
before the diagnostic increment is committed. Final ordinary CI remains the
author's integration gate.

## Source findings

- Sampling resets paired crash/registration files for every plain or race
  draw. Triage and Cedar create separate sibling oracle copies. Their
  frontend input remains the original semantic directory; Cedar preserves
  its original package GOPATH. There is no recover wrapper or semantic
  frontend exposure to the crash helper.
- Kind, message and output queries all receive the same two evidence
  paths. All three tools require valid registration and an empty crash
  report on success. Missing registration, setup exit 78, timeout and other
  non-verdict oracle exits refuse before comparison. Raw stdout and stderr
  remain separate files. Shell variables contain encoded JSON or quoted
  diagnostics, not raw message/output bytes.
- Triage's `.out` check matches the inspected pinned
  `deps/go/src/cmd/internal/testdir/testdir_test.go` `checkExpectedOutput`
  rule: CRLF normalization of actual bytes, otherwise exact comparison,
  and missing expected file means empty output. Its retained concatenation
  order is stdout then stderr; this does not reconstruct inter-descriptor
  ordering. Successful stdout outside the model observable is explicitly
  flagged. Cedar checks raw sizes for its silence rule; NUL and trailing
  LF cannot disappear into command substitution.
- Domains remain explicit: sampling accepts ok/panic, triage additionally
  fatal/deadlock, Cedar additionally deadlock and refuses fatal. The shared
  fatal-during-unwind ambiguity remains a named inability to observe, never
  a panic/conformance success. This preserves the bounded K3 disposition
  in `ab2ad4d5`; it is not B7 equivalence or an O2 admission change.
- Invalid UTF-8 message/output encoding still refuses. No policy widening,
  oracle/toolchain repin, baseline edit or semantic model repair is part of
  this increment. The ordinary CI step calls the actual diagnostic gate
  and propagates its failure.

## Fresh independent probes

Command, from the reviewer's own worktree:

```sh
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped python3 docs/evidence/2026-09-06_observer-diagnostic-review/probe.py
```

`probe-2.log` records exit 0 and **15 fresh checks** using a private build
of the frozen helper and source-extracted actual shell paths:

1. Each tool executes a two-file package with NUL/SOH/CR/LF output and a
   multiline panic. The exact first-line message and output survive; the
   sampling execution uses `-race`. Both original Go files remain exact,
   and removing the single oracle insertion restores each copied file.
2. Each tool observes an authentic initializer panic before registration,
   while initializer `os.Exit(0)` refuses missing acknowledgement. This
   exercises the intentional raw fallback and success boundary separately.
3. Each tool rejects oracle exits 124 and 137 even when the fake oracle
   returns a complete previously captured panic and valid paired crash
   evidence. Each invocation also checks that stale files were reset.

`results.json` retains exact result/raw bytes, exits and scratch location.
The initial `probe.log` is a reviewer extraction bug: a multiline
`one_line` function was initially copied as its header alone. No product
finding or gate failure is inferred from it; extraction was corrected and
all checks rerun. The failed log is retained.

The author's copied `hybrid-gate-final.log` records 105 focused checks
(66 synthetic and 39 native) and five syntactically valid mutations exposing
false acceptance. I inspected its actual extraction, checks and mutations;
I did not rerun that suite or duplicate the full corpus. Its limits remain
apparatus validation, and the shared core's separate full differential is
still an independent acceptance requirement.
