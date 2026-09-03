// noodler probes — type-assertion panic texts across the static/dynamic
// type matrix (spec#Type_assertions, spec#Run_time_panics; R9 pins gc's
// realized strings).
package main

type T struct{ n int }

func (t T) M() int   { return t.n }
func (t *T) PM() int { return t.n }

type I interface{ M() int }
type PI interface{ PM() int }
type Other interface{ Other() int }

// Dynamic *T asserted to T.
func assertPointerToValue() int {
	var x any = &T{1}
	return x.(T).n
}

// Dynamic T asserted to *T.
func assertValueToPointer() int {
	var x any = T{1}
	return x.(*T).n
}

// Dynamic T lacks the pointer-receiver method.
func assertValueMissingPointerMethod() int {
	var x any = T{1}
	return x.(PI).PM()
}

// Dynamic *T has both methods: succeeds.
func assertPointerHasBoth() (int, int) {
	var x any = &T{2}
	return x.(I).M(), x.(PI).PM()
}

// Static type is a named interface; dynamic type mismatch.
func assertNamedInterfaceMismatch() int {
	var i I = T{1}
	return i.(*T).n
}

// Static named interface, nil, asserted to another interface.
func assertNilNamedToInterface() int {
	var i I
	return i.(Other).Other()
}

// Static any, nil, asserted to an interface type.
func assertNilAnyToInterface() int {
	var x any
	return x.(I).M()
}

// Dynamic type is a defined non-struct type.
type Code int

func assertDefinedIntMismatch() int {
	var x any = Code(3)
	return x.(int)
}

// Dynamic type is a slice type.
func assertSliceMismatch() int {
	var x any = []int{1}
	return x.(int)
}

// Dynamic type is a func type.
func assertFuncMismatch() int {
	var x any = func() {}
	return x.(int)
}

// Dynamic type is a map type asserted to an interface with a method.
func assertMapToInterface() int {
	var x any = map[string]int{}
	return x.(I).M()
}

// Dynamic type is a pointer to a defined int.
func assertPointerDefinedInt() int {
	c := Code(4)
	var x any = &c
	return x.(int)
}

// Comma-ok forms never panic: the same matrix as booleans.
func commaOkMatrix() (bool, bool, bool, bool, bool) {
	var a any = &T{1}
	var b any = T{1}
	var n I
	_, ok1 := a.(T)
	_, ok2 := b.(PI)
	_, ok3 := a.(PI)
	_, ok4 := n.(Other)
	_, ok5 := b.(I)
	return ok1, ok2, ok3, ok4, ok5
}

// Type switch mirrors the matrix without panicking.
func typeSwitchMatrix() int {
	xs := []any{T{1}, &T{2}, Code(3), []int{}, nil}
	r := 0
	for _, x := range xs {
		switch x.(type) {
		case T:
			r += 1
		case *T:
			r += 10
		case Code:
			r += 100
		case []int:
			r += 1000
		case nil:
			r += 10000
		}
	}
	return r
}

func main() {}
