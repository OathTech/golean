// FR-24 witness (rowed 2026-09-04 from the FR-22/FR-23 slice's cedar-go
// re-run): a SOURCE-THROUGH library function whose reach walk pulls in a
// library package-level VARIABLE whose TYPE does not lower —
// encoding/binary.Write → dataSize → `var structSize sync.Map` — refuses
// the WHOLE export at collectGlobals ("sync.Map (only Mutex/RWMutex/
// WaitGroup/Once are modeled)"), even though the subject below never
// calls binary.Write. Shape lifted from cedar-go types/record.go:35
// (Record hashing). Legal Go; gc PASS expected.
package main

import (
	"bytes"
	"encoding/binary"
)

func hashLike(v uint64) int {
	var buf bytes.Buffer
	_ = binary.Write(&buf, binary.LittleEndian, v)
	return buf.Len()
}

func unrelatedToTheLibraryVar() int { return 42 }

func main() { println(unrelatedToTheLibraryVar(), hashLike(7)) }
