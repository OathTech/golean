package main

// Sweep S12 — long string payloads (matrix cells I01, I05; lane
// sweep/s12-panic-recover, 2026-10-27): an 8 KiB single-line payload is
// printed whole on the first line; the same text with an LF in the middle
// stops the first line at the LF (`printindented`; the first-line scope of
// docs/2026-07-25_unwinding-arc.md §A3). The machine: `stringFirstLine?`.

func eightKiB() string {
	s := ""
	for i := 0; i < 1024; i++ {
		s += "abcdefgh"
	}
	return s
}

func abortLongString() { panic(eightKiB()) }

func abortLongMultiline() {
	s := eightKiB()
	panic(s + "\n" + s)
}

func main() {}
