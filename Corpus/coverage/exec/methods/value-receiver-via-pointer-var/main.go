package main

// BUG-048 pin (FIXED 2026-08-08): calling a VALUE-receiver method
// through a pointer-typed VARIABLE (`p := &x; p.get()` — Go
// auto-dereferences: (*p).get()) used to wrong-stick the machine
// ("expected struct value, got addr") while go run returned normally.
// Surfaced by the goose-parity import of unittest/embedded.go;
// minimized here; both rows now pin the fixed auto-deref behavior
// green. See docs/BUGS.md BUG-048.

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
