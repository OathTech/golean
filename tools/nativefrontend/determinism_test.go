package main

// BUG-091 guard (2026-09-04, lane fr22-fr23 on the hygiene-a-series
// finding): the emitter's OUTPUT — the wire bytes, or the refusal text
// when it refuses — must be a function of the source alone. A `for … :=
// range <map>` whose iteration order reaches an emitted string or wire
// field makes the wire nondeterministic across runs (measured on main
// before the fix: a 2-label goto program refused naming "next" 26 times
// and "fallback" 4 times out of 30). This test emits a fixed set of
// programs N times and asserts byte-identical output; it was RED on
// main's emitter for the goto shape (docs/evidence/2026-09-04_fr22-fr23/
// bug091-red-first.txt) and is the bug's standing guard.

import (
	"encoding/json"
	"strings"
	"testing"
)

// The 2-label goto shape: both labels are goto targets NOT at the
// function body's top level (inside the `if`), so the refusal loop over
// e.gotoLabels names one of them — whichever the map yields first.
const detGotoSrc = `package main

func f(n int) int {
	if n > 0 {
	next:
		n--
		if n > 3 {
			goto next
		}
	fallback:
		n += 2
		if n < 0 {
			goto fallback
		}
	}
	return n
}

func main() { println(f(5)) }
`

// A multi-error shape: several declarations quarantine (each carries its
// own refusal text into the wire), an interface with an opaque generic
// requirement, a poisoned package-level var, imported method-set stubs,
// promotion wrappers — every table the emitter sorts or should sort.
const detMultiSrc = `package main

import (
	"iter"
	"os"
	"time"
)

type Bag struct{ items []int }

func (b Bag) All() iter.Seq[int] {
	return func(yield func(int) bool) {
		for _, v := range b.items {
			if !yield(v) {
				return
			}
		}
	}
}

func (b Bag) Bad(c complex128) int { return int(real(c)) }

type Iterable interface{ All() iter.Seq[int] }

type Outer struct {
	Bag
	tag string
}

var env = os.Getenv("GOLEAN_NEVER_SET")
var when = time.Date(2020, 1, 1, 0, 0, 0, 0, time.UTC)
var later = when

func useEnv() int   { return len(env) }
func useLater() bool { return later.IsZero() }
func useOuter() bool {
	_, ok := any(Outer{tag: "x"}).(Iterable)
	return ok
}

func main() { println(useEnv(), useLater(), useOuter()) }
`

// emitOnce returns the canonical bytes of one emission: the wire as JSON,
// or the refusal text.
func emitOnce(t *testing.T, src string) string {
	t.Helper()
	program, err := emitSource(t, src)
	if err != nil {
		return "REFUSED: " + err.Error()
	}
	b, jerr := json.Marshal(program)
	if jerr != nil {
		t.Fatalf("marshal: %v", jerr)
	}
	return string(b)
}

func TestEmitIsDeterministic(t *testing.T) {
	const runs = 20
	for _, tc := range []struct{ name, src string }{
		{"goto-two-labels", detGotoSrc},
		{"multi-quarantine", detMultiSrc},
	} {
		first := emitOnce(t, tc.src)
		for i := 1; i < runs; i++ {
			if got := emitOnce(t, tc.src); got != first {
				t.Fatalf("%s: emission %d differs from emission 0 (BUG-091: a map iteration order reached the output)\n--- 0:\n%.400s\n--- %d:\n%.400s", tc.name, i, first, i, got)
			}
		}
	}
	// The goto shape lands as a per-declaration STUB whose refusal text
	// names a label; it must be the alphabetically-first one — the
	// sorted order, not the map's (this is the byte that flipped on main).
	if got := emitOnce(t, detGotoSrc); !strings.Contains(got, `"goto target label fallback not at function body top level"`) {
		t.Fatalf("goto shape: stub does not name the sorted-first label: %.400s", got)
	}
}
