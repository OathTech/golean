package main

import "sync/atomic"

// TYPED ATOMICS (atomics arc wave 1): atomic.Int32/Int64/Uint32/Uint64/
// Uintptr ride the E5-T shadow model whose method bodies are gc's own
// type.go definitions (`Load` = `LoadInt64(&x.v)`, …), so a method call
// lowers through the SAME atomic-op node as the direct call — the
// identity principle. These rows pin the value semantics, the zero
// value, the VALUE semantics of the wrapper struct (a copy carries the
// count, exactly gc — vet's noCopy is not runtime behavior), the empty
// composite literal, a wrapper inside a struct, and the nil-receiver
// panic.

func typedInt64() int {
	var c atomic.Int64
	c.Store(40)
	c.Add(5)
	old := c.Swap(50)  // 45
	ok := c.CompareAndSwap(50, 60)
	v := 0
	if ok {
		v = 1000
	}
	return v + int(old)*10 + int(c.Load()) // 1000 + 450 + 60 = 1510
}

func typedInt32Wrap() int {
	var c atomic.Int32
	c.Store(2147483647)
	if c.Add(1) != -2147483648 {
		return 1
	}
	return int(c.Load()) + 2147483648 // 0
}

func typedUint32() int {
	var c atomic.Uint32
	c.Add(^uint32(0)) // decrement the zero value: MaxUint32
	return int(c.Load() >> 30) // 3
}

func typedUint64() int {
	var c atomic.Uint64
	c.Store(1 << 62)
	c.Add(1 << 62) // 1<<63
	return int(c.Load() >> 61) // 4
}

func typedUintptr() int {
	var c atomic.Uintptr
	c.Store(24)
	return int(c.Add(8)) // 32
}

// The zero value of a typed atomic is zero, and a struct COPY carries
// the value (Go value semantics — probe-verified: gc's wrapper is a
// plain struct around the word).
func typedZeroAndCopy() int {
	var a atomic.Int64
	z := a.Load() // 0
	a.Add(9)
	b := a // a copy: carries 9; further ops are independent
	b.Add(1)
	return int(z)*100 + int(a.Load())*10 + int(b.Load()) // 0 + 90 + 10 = 100
}

// The empty composite literal — the only legal cross-package literal
// (non-exported fields) — is the zero value; `&atomic.Int64{}` is an
// allocation of it.
func typedEmptyLiteral() int {
	a := atomic.Int32{}
	p := &atomic.Int64{}
	a.Add(3)
	p.Add(4)
	return int(a.Load())*10 + int(p.Load()) // 34
}

// A typed atomic as a struct FIELD, addressed through the enclosing
// struct's pointer.
type counter struct {
	name string
	hits atomic.Int64
	misses atomic.Int32
}

func typedStructField() int {
	c := &counter{name: "c"}
	c.hits.Add(2)
	c.hits.Add(3)
	c.misses.Store(-1)
	return int(c.hits.Load())*10 + int(c.misses.Load()) // 50 - 1 = 49
}

// A method call on a nil *atomic.Int64: the address of x.v is formed
// from nil — gc's recoverable nil-dereference runtime error.
func typedNilReceiver() int {
	var p *atomic.Int64
	return int(p.Load())
}

func main() {
	typedInt64()
	typedInt32Wrap()
	typedUint32()
	typedUint64()
	typedUintptr()
	typedZeroAndCopy()
	typedEmptyLiteral()
	typedStructField()
}
