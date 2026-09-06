# Fatal unwinding is accepted as panic

[AGENT], independent reviewer `typed-preflight`, 2026-09-06 UTC.
**Confirmed false acceptance in the initial diagnostic candidate and the
frozen core observer.** This adds a finding after the historical, bounded
byte-transport review in `../2026-09-06_observer-review/`; it does not alter
that sealed evidence or expand its preserved-policy verdict into terminal
classifier completeness.

The following valid program was run with the pinned Go 1.26.5 oracle:

```go
package main
import "sync"
func main() {
    var m sync.Mutex
    defer m.Unlock()
    panic("original")
}
```

The runtime begins unwinding the original panic, then terminates fatally
when the deferred call unlocks an unlocked mutex. Its stderr contains an
initial `panic: original` line and a later
`fatal error: sync: unlock of unlocked mutex` continuation. `go run` exits
1 and reports child exit 2.

Five independently executed, source-extracted observer paths instead
accepted the report as `status=panic`, `message=original`, returning 0:

| Path | Raw record |
| --- | --- |
| Standalone `membership-sampling` oracle | `fatal-red.json` |
| `gotest-triage` oracle block | `fatal-red.json` |
| `cedar-census` oracle block | `fatal-red.json` |
| Core `membership_go_observation`, allowed status `panic` | `core-fatal-red.json` |
| Core strict classification, expected `panic`, reason `original` | `core-strict-fatal-red.json` |

These probes used real Go processes and runtime reports, not a fake oracle.
The exact extracted shell sources, Go source, separate raw descriptors and
observer stdout/stderr are retained in the evidence archive. Initial
diagnostic source hashes are in `provenance.json`; core runner hash is
`0c545a40ac6a71cac8ede219437482c93210eec8f3dc75ab01660b3f48037a81`, matching
the earlier frozen byte-transport candidate over `ff7173dd`.

This is inherited classifier behavior, exposed during review of the
diagnostic byte-transport repair. Selecting the first panic message is
insufficient to determine terminal status. The panic splitter accepts that
initial block even when a fatal continuation follows. A manifest expecting
panic can consequently hide a model that misses the fatal outcome.

The first proposed remedy, broad substring priority for fatal, is also
insufficient. A panic payload may contain `fatal error: `, and program
output can print that text. Independent real-Go probes additionally confirm
that `panic("original\nfatal error: sync: unlock of unlocked mutex")` and
the actual fatal-unwind example have **byte-identical leading lines before
the goroutine header** (`marker-collisions.json`). Their complete stack
reports differ; no complete-report byte identity is claimed. A helper using
only those leading lines cannot distinguish these outcomes.

Required resolution: use a documented line/block-aware classification
contract, preserve ordinary marker text as payload/output where its role
is unambiguous, and explicitly refuse mixed-line ambiguity. Do not promote
an expected/allowed manifest status into evidence for the actual terminal
status. Add wrong-expected-status, wrong-allowed-status, marker-in-payload,
marker-in-output and multiline-collision controls, not only positive fatal
message extraction controls. This does not require an invalid-UTF-8 or R-1
rendering-policy decision.

The parent directed a separate red-first core classifier increment after
the frozen byte-transport CI, with fresh validation appropriate to its
source changes. The core repair is **open at this finding checkpoint** and
must not be inferred complete from the diagnostic repair or the historical
byte-transport PASS. Diagnostic repair/re-review status is recorded in the
companion README and green records when present.
