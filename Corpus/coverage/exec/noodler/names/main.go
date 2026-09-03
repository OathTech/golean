// noodler probes — name resolution edges: predeclared identifiers are
// ordinary universe-scope names that may be shadowed (spec#Predeclared_identifiers,
// spec#Declarations_and_scope), labels live in their own namespace
// (spec#Labeled_statements), identifiers may be any Unicode letters
// (spec#Identifiers).
package main

// Shadowing `len` locally: the builtin is unreachable, the variable wins.
func shadowLen() int {
	len := 5
	return len + 1
}

// Shadowing `true`/`false` locally.
func shadowTrue() int {
	true := false
	if true {
		return 1
	}
	return 2
}

// Shadowing `nil` with an int.
func shadowNil() int {
	nil := 7
	return nil * 2
}

// Shadowing a type name (`string`, `int`) with variables.
func shadowTypeNames() (int, int) {
	string := 3
	int := 4
	return string + int, string * int
}

// Shadowing `iota` inside a const block with a local const named iota.
func shadowIota() int {
	const iota = 100
	const (
		a = iota
		b
	)
	return a + b
}

// Shadowing `append`/`copy`/`make` with local funcs.
func shadowBuiltinFuncs() int {
	append := func(x int) int { return x + 1 }
	copy := func(x int) int { return x * 2 }
	make := 10
	return append(copy(make))
}

// Package-level shadowing: a package var named `cap`; `len` still works.
var cap = 42

func packageLevelCapVar() int {
	s := []int{1, 2, 3}
	return cap + len(s)
}

// Labels and variables of the same name coexist.
func labelVsVariable() int {
	x := 0
x:
	for i := 0; i < 10; i++ {
		x += i
		if x > 5 {
			break x
		}
	}
	return x
}

// Unicode identifiers.
func unicodeIdentifiers() (int, float64) {
	π := 3.0
	变量 := 4
	ñandú := 5
	return 变量 + ñandú, π * 2
}

// Function-local defined types participate in type switches and
// assertions (no generics involved).
func localTypeInTypeSwitch() int {
	type celsius int
	type label string
	var xs []any = []any{celsius(3), label("l"), 3, "l"}
	sum := 0
	for _, x := range xs {
		switch v := x.(type) {
		case celsius:
			sum += int(v) * 100
		case label:
			sum += len(v) * 10
		case int:
			sum += v
		case string:
			sum += 1000
		}
	}
	return sum
}

// Blank identifier as a receiver name and parameter name.
type blankRecv struct{ v int }

func (_ blankRecv) Get(_ int, y int) int { return y * 3 }

func blankNames() int {
	var _ = 5
	_, b := 1, 2
	return blankRecv{}.Get(99, b)
}

// A parameter named like the package's own function.
func shadowFuncName() int {
	shadowLen := 3
	return shadowLen
}

// Method named like a builtin.
type lenner struct{ n int }

func (l lenner) len() int { return l.n }
func (l lenner) cap() int { return l.n * 2 }

func methodNamedLikeBuiltin() int {
	l := lenner{4}
	return l.len() + l.cap() + len([]int{1})
}

// Redeclaration in := with at least one new variable; the old one is
// reassigned in the same scope.
func shortRedeclare() (int, int) {
	a, b := 1, 2
	a, c := 10, 3
	return a + b, c
}

// Shadowing in an if-init with the same name as the outer variable.
func ifInitShadow() int {
	x := 1
	if x := x + 10; x > 5 {
		return x
	}
	return x
}

func main() {}
