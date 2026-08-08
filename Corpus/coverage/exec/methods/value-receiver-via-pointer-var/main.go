package main

// BUG-048 pin: calling a VALUE-receiver method through a pointer-typed
// VARIABLE (`p := &x; p.Get()` — Go auto-dereferences: (*p).Get()) gets
// the machine STUCK ("expected struct value, got addr") while go run
// returns normally. Surfaced by the goose-parity import of
// unittest/embedded.go (the explicit `d.embedB.Foo()` selector through
// a pointer-embedded field is the same class); minimized here.
// See docs/BUGS.md BUG-048.

type sVal struct{ v int }

func (s sVal) get() int { return s.v }

func valueRecvViaPointerVar() int {
	x := sVal{v: 3}
	p := &x
	return p.get()
}

func valueRecvViaPointerLiteral() int {
	p := &sVal{v: 4}
	return p.get()
}

func main() {
	valueRecvViaPointerVar()
}
