// noodler probes — generics edges (spec#Type_parameter_declarations,
// spec#Type_inference, spec#Instantiations, spec#Type_constraints).
package main

import "cmp"

type Number interface {
	~int | ~int64 | ~float64
}

func Max[T cmp.Ordered](a, b T) T {
	if a > b {
		return a
	}
	return b
}

// Untyped constant inference: mixed 1 and 2.5 infer float64 (Go 1.21).
func inferMixedUntypedConstants() (float64, bool) {
	m := Max(1, 2.5)
	var check any = m
	_, isF := check.(float64)
	return m, isF
}

// Untyped rune and int constants infer rune (int32).
func inferRuneAndInt() (int32, bool) {
	m := Max('a', 1)
	var check any = m
	_, isR := check.(int32)
	return m, isR
}

// Zero value of a type parameter via var and via *new(T).
func Zero[T any]() (T, T) {
	var z T
	return z, *new(T)
}

func zeroOfTypeParams() (int, string, bool, float64) {
	a, _ := Zero[int]()
	_, b := Zero[string]()
	c, _ := Zero[bool]()
	_, d := Zero[float64]()
	return a, b, c, d
}

// Zero value of a pointer/slice/map/interface type parameter is nil.
func zeroNilKinds() (bool, bool, bool, bool) {
	p, _ := Zero[*int]()
	s, _ := Zero[[]int]()
	m, _ := Zero[map[int]int]()
	i, _ := Zero[any]()
	return p == nil, s == nil, m == nil, i == nil
}

// Instantiation with an interface type argument: comparable on any.
func Eq[T comparable](a, b T) bool { return a == b }

func instantiateWithInterface() (bool, bool, bool) {
	return Eq[any](1, 1), Eq[any](1, int64(1)), Eq[any]("a", "a")
}

// Instantiation with a defined type under a ~ constraint.
type Celsius float64

func Sum[T Number](xs ...T) T {
	var s T
	for _, x := range xs {
		s += x
	}
	return s
}

func tildeConstraintDefinedType() (Celsius, bool) {
	s := Sum(Celsius(1.5), Celsius(2.5))
	var check any = s
	_, ok := check.(Celsius)
	return s, ok
}

// Generic type with methods; method on a generic type returns zero of T.
type Stack[T any] struct{ items []T }

func (s *Stack[T]) Push(x T) { s.items = append(s.items, x) }
func (s *Stack[T]) Pop() (T, bool) {
	var zero T
	if len(s.items) == 0 {
		return zero, false
	}
	x := s.items[len(s.items)-1]
	s.items = s.items[:len(s.items)-1]
	return x, true
}

func genericStackOps() (int, bool, string, bool) {
	var si Stack[int]
	si.Push(3)
	si.Push(4)
	a, _ := si.Pop()
	var ss Stack[string]
	b, okb := ss.Pop()
	_, _ = si.Pop()
	_, oka := si.Pop()
	return a, oka, b, okb
}

// Generic function value assigned to a variable then called.
func genericFuncValue() int {
	f := Max[int]
	g := Max[string]
	return f(3, 9) + len(g("aa", "b"))
}

// Conversions inside a generic body between type parameter and int.
func ToInt[T Number](x T) int { return int(x) }

func conversionInGenericBody() (int, int) {
	return ToInt(3.9), ToInt(Celsius(-2.5))
}

// Type switch on any(x) inside a generic function.
func Kind[T any](x T) int {
	switch any(x).(type) {
	case int:
		return 1
	case string:
		return 2
	case []T:
		return 3
	default:
		return 4
	}
}

func typeSwitchInGeneric() (int, int, int, int) {
	return Kind(1), Kind("s"), Kind([]int{}), Kind(1.5)
}

// Generic struct embedded in a concrete struct: promoted method.
type Named struct {
	Stack[int]
	name string
}

func embeddedGenericPromotion() (int, int) {
	n := Named{name: "n"}
	n.Push(7)
	n.Push(8)
	x, _ := n.Pop()
	return x, len(n.items)
}

// Generic alias (Go 1.24): type Set[T] = map[T]struct{}.
type Set[T comparable] = map[T]struct{}

func genericAlias() (int, bool) {
	s := Set[string]{}
	s["a"] = struct{}{}
	s["b"] = struct{}{}
	s["a"] = struct{}{}
	_, ok := s["b"]
	return len(s), ok
}

// Generic min over a defined string type.
type Name string

func minDefinedString() Name {
	return Max(Name("apple"), Name("banana"))
}

// Constraint with a method: call through the type parameter.
type Stringer interface{ String() string }

type ID int

func (i ID) String() string { return "id" }

func Describe[T Stringer](x T) string { return x.String() + "!" }

func methodConstraintCall() string {
	return Describe(ID(4))
}

// Type parameter used as a map key and value.
func Invert[K, V comparable](m map[K]V) map[V]K {
	r := map[V]K{}
	for k, v := range m {
		r[v] = k
	}
	return r
}

func typeParamMapKeyValue() (int, string) {
	inv := Invert(map[string]int{"a": 1, "b": 2})
	return len(inv), inv[2]
}

// Generic recursion.
func Len[T any](xs []T) int {
	if len(xs) == 0 {
		return 0
	}
	return 1 + Len(xs[1:])
}

func genericRecursion() int {
	return Len([]string{"a", "b", "c"}) + Len([]int{})
}

// Comparable constraint with array-of-interface type argument panics at
// runtime on uncomparable dynamic values.
func comparableArrayOfIface() bool {
	return Eq([1]any{[]int{1}}, [1]any{[]int{1}})
}

// Generic function returning multiple type-param results.
func Swap[A, B any](a A, b B) (B, A) { return b, a }

func genericSwap() (string, int) {
	return Swap(1, "one")
}

// Type parameter with core type string: len and indexing work.
func First[S ~string](s S) byte { return s[0] }

func coreTypeString() byte {
	return First(Name("zeta"))
}

func main() {}
