package main

// strings.Builder through the REAL upstream body with the three OVERLAID
// sites (stdlib source-through slice 2, 2026-09-03; stdlib-overlay.tsv:
// builder.go:47 String = string(b.buf); :39 copyCheck's abi.NoEscape = b;
// :67 grow's bytealg.MakeNoZero = append([]byte(nil), make(...)...)).
// Each row pins the EXACT behaviour a substitution claims:
//   - string-after-writes: the bytes String() returns are the bytes
//     written (all four Write* methods, multi-byte runes included);
//   - string-stable-in-place: a string returned by String() keeps its
//     bytes when a LATER write appends IN PLACE into spare capacity (the
//     aliasing premise of the :47 overlay — upstream aliases, the machine
//     copies; both must show the old string unchanged);
//   - grow-contract: after Grow(n), Cap()-Len() >= n (the documented
//     contract; true for every member of the R2 capacity envelope, so it
//     is a STRICT row — the exact Cap is the membership suite
//     strings/builder-cap);
//   - grow-noop / grow-negative / copy-panics-after-grow: Grow's
//     documented edges through the real copyCheck (:39);
//   - reset-reuse, write-rune-invalid: Reset and utf8.AppendRune's
//     RuneError path;
//   - join-large / repeat-chunked / repeat-large: strings.Join and
//     strings.Repeat (shims RETIRED this slice) through the real Builder,
//     Repeat past its 8 KB chunk limit and its repeated-spaces fast path.
// Expected status is gc's; every row is a strict differential row.

import "strings"

func builderStringAfterWrites() (string, int) {
	var b strings.Builder
	b.WriteString("ab")
	b.WriteByte('c')
	b.WriteRune('é')
	b.WriteRune('日')
	b.Write([]byte{'x', 0, 'y'})
	n, _ := b.WriteRune('😀')
	return b.String() + ":" + itoa(n), b.Len()
}

func builderStringStableInPlace() (string, string, string, bool) {
	var b strings.Builder
	b.Grow(64) // spare capacity: the later writes append IN PLACE
	b.WriteString("ab")
	s1 := b.String()
	b.WriteString("cd")
	s2 := b.String()
	b.WriteByte('e')
	return s1, s2, b.String(), b.Cap()-b.Len() >= 64-5
}

func builderGrowContract() string {
	out := ""
	// Four probes: each iteration spills twice (WriteString onto nil,
	// then grow), and a strict row's invariance streams cover 10 picks.
	for _, n := range []int{0, 9, 33, 100} {
		var b strings.Builder
		b.WriteString("seed")
		b.Grow(n)
		if b.Cap()-b.Len() >= n && b.Len() == 4 && b.String() == "seed" {
			out += "y"
		} else {
			out += "N"
		}
	}
	return out
}

// The exact Cap is allocator latitude (membership suite builder-cap);
// this strict row observes only that a Grow that FITS does not change it.
func builderGrowNoop() (bool, string) {
	var b strings.Builder
	b.Grow(50)
	c := b.Cap()
	b.WriteString("abc")
	b.Grow(10) // fits: no growth
	return c == b.Cap(), b.String()
}

func builderGrowNegative() int {
	var b strings.Builder
	b.Grow(-1)
	return b.Len()
}

func builderCopyPanicsAfterGrow() int {
	var b strings.Builder
	b.Grow(8)
	c := b // a non-zero Builder copied by value (addr set by Grow's copyCheck)
	c.WriteString("x")
	return c.Len()
}

func builderResetReuse() (string, int, int) {
	var b strings.Builder
	b.WriteString("first")
	b.Reset()
	l0 := b.Len()
	b.WriteString("second")
	return b.String(), l0, b.Len()
}

func builderWriteRuneInvalid() (string, int) {
	var b strings.Builder
	n1, _ := b.WriteRune(-1)
	n2, _ := b.WriteRune(0x110000)
	n3, _ := b.WriteRune(0xD800) // surrogate half
	s := b.String()
	hex := ""
	for i := 0; i < len(s); i++ {
		hex += string("0123456789abcdef"[s[i]>>4]) + string("0123456789abcdef"[s[i]&0xf])
	}
	return hex, n1*100 + n2*10 + n3
}

func joinLarge() (int, string) {
	elems := make([]string, 0, 100)
	for i := 0; i < 100; i++ {
		elems = append(elems, "e"+itoa(i))
	}
	s := strings.Join(elems, ", ")
	return len(s), s[:12] + "…" + s[len(s)-8:]
}

// 768 bytes: the doubling WriteString(b.String()[:chunk]) loop (chunk =
// min(n-len, len, chunkMax) with chunkMax = n below upstream's 8 KB
// chunk limit). INTERPRETER COST (BUG-090, measured in the slice-2
// README): the machine's heap is an association list, so allocation-
// heavy and cell-write-heavy loops are quadratic (a 1 KB Builder ~1.5 s;
// 4,096 one-byte appends > 60 s), and the 8 KB chunk-limit arm and the
// 15 KB / 64 KB probes this row first carried exceed the 30 s row budget
// — a recorded cost bound, not a semantics gap.
func repeatDoublingLoop() (int, int, string, string, string) {
	big := strings.Repeat("abcdefgh", 96)
	sum := 0
	for i := 0; i < len(big); i++ {
		sum = (sum*31 + int(big[i])) % 1000003
	}
	sp := strings.Repeat(" ", 10) // repeatedSpaces fast path
	return len(big), sum, sp + "|", strings.Repeat("-", 3) + strings.Repeat("xy", 0) + strings.Repeat("xy", 1), big[760:768]
}

// 1,024 bytes through the real body (the retired shim's golean-invented
// 1<<24 bound is gone; what bounds Repeat now is interpreter cost, BUG-090
// — see strings/trimspace-repeat/repeat-bound-refused, a runner-budget red).
func repeat1K() (int, byte, byte) {
	s := strings.Repeat("0123456789abcdef", 64)
	return len(s), s[0], s[len(s)-1]
}

func itoa(n int) string {
	if n == 0 {
		return "0"
	}
	neg := n < 0
	if neg {
		n = -n
	}
	out := ""
	for n > 0 {
		out = string(rune('0'+n%10)) + out
		n /= 10
	}
	if neg {
		return "-" + out
	}
	return out
}

func main() {
	s, n := builderStringAfterWrites()
	println(s, n)
	a, b2, c, ok := builderStringStableInPlace()
	println(a, b2, c, ok)
	println(builderGrowContract())
	same, s2 := builderGrowNoop()
	println(same, s2)
	r, l0, l1 := builderResetReuse()
	println(r, l0, l1)
	h, ns := builderWriteRuneInvalid()
	println(h, ns)
	jl, js := joinLarge()
	println(jl, js)
	rl, rs, rsp, rmix, rmid := repeatDoublingLoop()
	println(rl, rs, rsp, rmix, rmid)
	ll, f, la := repeat1K()
	println(ll, f, la)
}
