// Anonymous-interface DISPLAY pins (lane fr19-bug097, 2026-09-05; design
// note docs/2026-09-05_fr19-bug097-design.md §1/§3): the machine renders
// an anonymous interface in panic texts from the wire's display record —
// gc's `NameString` spelling: `interface { A(); Z() }` (one space inside
// the braces, `; ` between methods, gc's CompareSyms order: exported
// first by name, then unexported by name; an unexported method
// qualified by package NAME; embedded interfaces flattened). Identity is
// the separate path-qualified key. Texts from the go1.26.5 probes in
// docs/evidence/2026-09-05_fr19-bug097/gc-probes.txt (P1).
package main

type T int

func (T) Get() int { return 1 }
func (T) get() int { return 1 }

type V int

func (V) Get() int { return 2 }

// gc: interface conversion: main.T is not interface { A(); Z() }: missing method A
func anonMissingOrder() int {
	var a any = T(1)
	_ = a.(interface {
		Z()
		A()
	})
	return 0
}

// gc: interface conversion: main.T is not interface { M(); main.get() int }: missing method M
func anonUnexported() int {
	var a any = T(1)
	_ = a.(interface {
		get() int
		M()
	})
	return 0
}

// An unexported-method requirement satisfied within the package.
func anonUnexportedSatisfied() (bool, int) {
	var a any = T(1)
	g, ok := a.(interface{ get() int })
	if !ok {
		return false, 0
	}
	return true, g.get()
}

// gc: interface conversion: main.T is not interface { Error() string; Get() int }: missing method Error
func anonEmbeddedFlattened() int {
	var a any = T(1)
	_ = a.(interface {
		error
		Get() int
	})
	return 0
}

// The operand's STATIC anonymous interface type is the source in the
// concrete-target form.
// gc: interface conversion: interface { Get() int } is main.T, not main.V
func anonSourceDisplay() int {
	var s interface{ Get() int } = T(1)
	return int(s.(V))
}

// gc: interface conversion: interface is nil, not interface { M() }
func anonNil() int {
	var n any
	_ = n.(interface{ M() })
	return 0
}

// An anonymous interface nested in a composite target.
// gc: interface conversion: interface {} is main.T, not []interface { M() }
func anonSliceTarget() int {
	var a any = T(1)
	return len(a.([]interface{ M() }))
}

// A method present with a DIFFERENT signature is reported as missing
// at runtime (gc's itab check); the display names the declared type
// inside the anonymous interface.
// gc: interface conversion: main.T is not interface { Get() main.T }: missing method Get
func anonNamedResult() int {
	var a any = T(1)
	_ = a.(interface{ Get() T })
	return 0
}

func main() {
	println(anonUnexportedSatisfied())
	for _, f := range []func() int{anonMissingOrder, anonUnexported, anonEmbeddedFlattened,
		anonSourceDisplay, anonNil, anonSliceTarget, anonNamedResult} {
		func() {
			defer func() { println(recover().(error).Error()) }()
			f()
		}()
	}
}
