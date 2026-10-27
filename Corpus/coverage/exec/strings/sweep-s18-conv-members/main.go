package main

// S18 sweep — the conversion capacity envelope (ChoiceSite.convCap, convCapMembers in
// Ops.lean; latitude inventory R3) at the lengths and operand routes NOT in strings/conv-cap:
// n = 1, the 128-byte table's first class (1017 → 1024), the page path (32769 → 40960), a
// slice of a constant (non-literal on both sides), a constant through a generic conversion
// (non-literal on both sides), a non-ASCII operand (bytes counted), and the rune buffer at
// n ∈ {0, 1, 9}. Membership rows: every gc draw is a member, members= pins the envelope's
// cardinality. Probe-verified go1.26.5, 2026-10-27.
var sinkB []byte
var sinkR []rune

type MyS string
type MyB []byte

const k = "hello"
const k2 = "world"

// A non-literal string of n bytes, built by doubling (no stdlib call, no pick).
//
//go:noinline
func mkN(n int) string {
	s := "a"
	for len(s) < n {
		s += s
	}
	return s[:n]
}

// A non-literal string of n two-byte runes.
//
//go:noinline
func mkE(n int) string {
	s := "é"
	for len(s) < 2*n {
		s += s
	}
	return s[:2*n]
}

// A non-literal string of n invalid bytes (each decodes as U+FFFD: n runes).
//
//go:noinline
func mkX(n int) string {
	s := "\xff"
	for len(s) < n {
		s += s
	}
	return s[:n]
}

//go:noinline
func id(s string) string { return s }

func convG[T ~string](s T) int {
	b := []byte(s)
	b[0] = 'x'
	return cap(b)
}

// gc 32; members {1, 8, 32}
func bytes1Mut() int {
	s := mkN(1)
	b := []byte(s)
	b[0] = 'x'
	return cap(b)
}

// gc 1024; members {1017, 1024}
func bytes1017Esc() int {
	s := mkN(1017)
	b := []byte(s)
	sinkB = b
	return cap(b)
}

// gc 40960 (the page path); members {32769, 40960}
func bytes32769Esc() int {
	s := mkN(32769)
	b := []byte(s)
	sinkB = b
	return cap(b)
}

// gc 32; members {2, 8, 32} (the frontend does not fold k[1:3])
func bytesConstSliceMut() int {
	b := []byte(k[1:3])
	b[0] = 'x'
	return cap(b)
}

// gc 32; members {5, 8, 32}
func bytesGenericConstMut() int {
	return convG(k)
}

// gc 8; members {6, 8, 32}
func bytesNonAsciiEsc() int {
	s := id("ééé")
	b := []byte(s)
	sinkB = b
	return cap(b)
}

// gc 32; members {2, 32}
func runes1Nomut() int {
	s := mkN(1)
	r := []rune(s)
	return cap(r)
}

// gc 12; members {12, 32}
func runes9Esc() int {
	s := mkN(9)
	r := []rune(s)
	sinkR = r
	return cap(r)
}
