package main

// Defect-neighbourhood campaign, shape S27 (byte transparency of
// string-carrying channels), lane sweep/s27-bytes, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, BUG-105 and BUG-138; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// (channel, goroutine, closure, struct field, array and slice element, pointer,
// interface box + assertion, generic function, method on a defined string type,
// package-level global) — the bytes must arrive unchanged.

const probe = "\xff\x00é\xed\xa0\x80😀"

var global = probe + "|g"

type box struct {
	S string
	A [2]string
}

type defined string

func (d defined) first() byte  { return d[0] }
func (d defined) tail() string { return string(d[1:]) }

func ident[T ~string](x T) T { return x }

func throughChannelAndGoroutine() (string, int, bool) {
	ch := make(chan string, 1)
	go func() { ch <- probe }()
	got := <-ch
	return got, len(got), got == probe
}

func throughClosureAndPointer() (string, bool, string) {
	s := probe
	p := &s
	f := func() string { return *p + "|c" }
	*p = probe + "!"
	return f(), s == probe+"!", *p
}

func throughStructArraySlice() (string, string, string, bool) {
	b := box{S: probe, A: [2]string{probe, "\x80"}}
	sl := []string{"\xc0\x80", probe}
	sl = append(sl, b.A[1])
	return b.S, b.A[0] + b.A[1], sl[0] + sl[2], sl[1] == b.S
}

func throughInterfaceAndAssert() (string, bool, int, string) {
	var x any = probe
	s, ok := x.(string)
	var d any = defined(probe)
	dd := d.(defined)
	return s, ok, len(s), string(dd)
}

func throughGenericAndMethod() (string, byte, string, string) {
	d := defined(probe)
	g := ident(d)
	return string(g), d.first(), d.tail(), ident(probe)
}

func throughGlobal() (string, int, bool) {
	return global, len(global), global[:len(probe)] == probe
}

func switchOnInvalidBytes() (int, int, int) {
	r1, r2, r3 := 0, 0, 0
	switch probe[:1] {
	case "\xfe":
		r1 = 1
	case "\xff":
		r1 = 2
	}
	switch probe[3:5] {
	case "é":
		r2 = 1
	default:
		r2 = 2
	}
	switch s := probe[5:8]; s {
	case "\xed\xa0\x80":
		r3 = 1
	case "\xef\xbf\xbd":
		r3 = 2
	}
	return r1, r2, r3
}

func main() {
	throughChannelAndGoroutine()
}

func throughDeferArg() (out string, n int) {
	defer func(s string) { out = s + "|d"; n = len(s) }(probe)
	return "unset", 0
}
