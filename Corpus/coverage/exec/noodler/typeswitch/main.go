// noodler probes — type switch clause selection (spec#Type_switches):
// the first matching clause wins; `case nil` matches only a nil
// interface; `case any` matches every non-nil value.
package main

type Reader interface{ Read() int }
type Writer interface{ Write() int }

type RW struct{}

func (RW) Read() int  { return 1 }
func (RW) Write() int { return 2 }

type R struct{}

func (R) Read() int { return 3 }

// Dynamic type implements both: the FIRST listed interface case wins.
func firstInterfaceCaseWins() (int, int) {
	var x any = RW{}
	a, b := 0, 0
	switch v := x.(type) {
	case Reader:
		a = v.Read()
	case Writer:
		a = v.Write()
	}
	switch v := x.(type) {
	case Writer:
		b = v.Write()
	case Reader:
		b = v.Read()
	}
	return a, b
}

// Concrete case listed after an interface case it implements: the
// interface case wins.
func interfaceBeforeConcrete() int {
	var x any = R{}
	switch x.(type) {
	case Reader:
		return 1
	case R:
		return 2
	}
	return 0
}

// case any matches non-nil values; nil matches only case nil.
func caseAnyVsNil() (int, int) {
	var x any = 1
	var n any
	r1, r2 := 0, 0
	switch x.(type) {
	case nil:
		r1 = 1
	case any:
		r1 = 2
	}
	switch n.(type) {
	case any:
		r2 = 2
	case nil:
		r2 = 1
	}
	return r1, r2
}

// Multi-type case binds the interface type; single-type case binds the
// concrete type.
func multiTypeCaseBinding() (int, int) {
	xs := []any{int8(3), int16(4), "s"}
	sum := 0
	strs := 0
	for _, x := range xs {
		switch v := x.(type) {
		case int8, int16:
			if w, ok := v.(int16); ok {
				sum += int(w) * 10
			} else {
				sum += int(v.(int8))
			}
		case string:
			strs += len(v)
		}
	}
	return sum, strs
}

// Type switch on a typed-nil pointer: matches the pointer type, not nil.
func typedNilPointerCase() int {
	var p *RW
	var x any = p
	switch x.(type) {
	case nil:
		return 1
	case *RW:
		return 2
	}
	return 3
}

// Type switch with a default in the middle and a fallthrough-free
// chain; default is chosen only when nothing matches.
func defaultInMiddle() (int, int) {
	f := func(x any) int {
		switch x.(type) {
		case int:
			return 1
		default:
			return 9
		case string:
			return 2
		}
	}
	return f("s"), f(2.5)
}

// Type switch over a defined interface type variable (not any).
func switchOnNamedInterface() int {
	var r Reader = RW{}
	switch v := r.(type) {
	case Writer:
		return v.Write() * 10
	case R:
		return 1
	}
	return 0
}

// Type switch on a generic-instantiated dynamic type.
type Box[T any] struct{ v T }

func switchOnGenericInstance() int {
	xs := []any{Box[int]{1}, Box[string]{"s"}}
	r := 0
	for _, x := range xs {
		switch b := x.(type) {
		case Box[int]:
			r += b.v
		case Box[string]:
			r += len(b.v) * 10
		}
	}
	return r
}

func main() {}
