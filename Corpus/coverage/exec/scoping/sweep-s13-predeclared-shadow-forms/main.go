package main

import "strings"

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: the predeclared
// identifiers BUG-069's rows do not hold (true/false/nil as locals are
// scoping/predeclared-shadow/*), shadowed LOCALLY as variables, parameters,
// types, constants, fields, methods and labels, and three non-universe names
// shadowed after their use (a package function, an imported package, the
// function's own name). emitIdent resolves by go/types object, never by name;
// each subject reads the shadow. The package-level shadows are
// scoping/sweep-s13-pkg-shadow-cap-iota (cap, iota) and, for the names the
// oracle harness itself uses (len, true, nil, false, bool), hand probes in the
// lane's report; a local INTERFACE type named error with a dispatched method
// is scoping/sweep-s13-local-iface-dispatch (BUG-301, born red). Expected = gc.

// B1
func lenVar() int {
	len := 3
	return len + 1 // 4
}

func takesLen(len int) int { return len * 2 }

// B2
func lenParam() int { return takesLen(21) } // 42

// B5
func appendVar() int {
	append := func(s []int, v int) []int { return []int{v} }
	s := append([]int{1, 2}, 9)
	return len(s)*10 + s[0] // 19
}

// B6a
func makeVar() int {
	make := 5
	return make * 2 // 10
}

// B6b
func newVar() int {
	new := func() *int { v := 8; return &v }
	return *new() // 8
}

// B6c
func copyVar() int {
	copy := "cp"
	return len(copy) // 2
}

// B6d
func deleteVar() int {
	delete := map[int]int{1: 1, 2: 2}
	return len(delete) // 2
}

// B6e
func panicVar() int {
	panic := 3
	return panic + 1 // 4
}

// B6f
func recoverVar() int {
	recover := func() int { return 11 }
	return recover() // 11
}

// B6g
func printVar() int {
	print := 2
	println := 3
	return print*10 + println // 23
}

// B6h
func minMaxVar() int {
	min, max := 9, 1
	return min*10 + max // 91: the variables, not the builtins
}

// B6i
func closeVar() int {
	close := true
	if close {
		return 1
	}
	return 0
}

// B6j
func clearVar() int {
	clear := []int{1, 2, 3}
	return len(clear) // 3
}

// B7a-h: the predeclared TYPE names as variables.
func intVar() int {
	int := 5
	return int + 1 // 6
}

func stringVar() int {
	string := "abc"
	return len(string) // 3
}

func boolVar() int {
	bool := 7
	return bool // 7
}

func byteVar() int {
	byte := 7
	return byte * 2 // 14
}

func runeVar() int {
	rune := 65
	return rune + 1 // 66
}

func errorVar() int {
	error := 3
	return error * 3 // 9
}

func anyVar() int {
	any := 4
	return any + 4 // 8
}

func float64Var() int {
	float64 := 2
	return float64 * 5 // 10
}

// B8a: a local type named int, and a conversion through it.
func intLocalType() string {
	type int string
	x := int("hi")
	return string(x) + "!" // "hi!"
}

// B8b: a local struct type named error.
func errorLocalStructType() int {
	type error struct{ code int }
	e := error{code: 42}
	return e.code // 42
}

// B9e: a local const true.
func trueLocalConst() int {
	const true = false
	if true {
		return 1
	}
	return 2 // 2
}

// B10a: iota as a variable.
func iotaVar() int {
	iota := 7
	return iota + 1 // 8
}

// B13: a shadowed builtin captured by a closure.
func lenCaptured() int {
	len := 1
	f := func() int { len++; return len }
	return f() + f() // 5
}

// B14: a pointer variable named nil.
func nilPointerVar() int {
	x := 9
	nil := &x
	*nil = 10
	return x // 10
}

func takesNil(nil []int) int { return len(nil) }

// B15: a slice parameter named nil.
func nilParam() int { return takesNil([]int{1, 2, 3}) } // 3

type oddFields struct {
	len  int
	nil  int
	true bool
}

// B16: fields named len, nil, true.
func fieldsNamedPredeclared() int {
	s := oddFields{len: 1, nil: 2, true: true}
	if s.true {
		return s.len*10 + s.nil // 12
	}
	return 0
}

type withLen struct{ n int }

func (w withLen) len() int { return w.n }

// B17: a method named len beside the builtin.
func methodNamedLen() int {
	w := withLen{n: 4}
	return w.len() + len([]int{1}) // 5
}

// B18: labels named nil and len.
func labelsNamedPredeclared() int {
	i := 0
nil:
	i++
	if i < 2 {
		goto nil
	}
len:
	i++
	if i < 4 {
		goto len
	}
	return i // 4
}

// B19: a local type rune over byte: []rune("ab") is a byte slice.
func runeLocalType() int {
	type rune byte
	rs := []rune("ab")
	return len(rs)*100 + int(rs[0]) // 297
}

// B20: a local type named any.
func anyLocalType() int {
	type any int
	var a any = 3
	return int(a) * 2 // 6
}

func helperNine() int { return 9 }

// B23: a package function's name shadowed by a local after its call.
func funcNameShadowedByVar() int {
	a := helperNine()
	helperNine := 1
	return a*10 + helperNine // 91
}

// B24: an imported package's name shadowed by a local after its use.
func importNameShadowed() int {
	u := strings.Repeat("a", 2)
	strings := 5
	if u == "aa" {
		return strings // 5
	}
	return 0
}

// B25: the function's own name shadowed by a local.
func ownNameShadowed() int {
	ownNameShadowed := 2
	return ownNameShadowed * 3 // 6
}

func main() {
	println(lenVar(), lenParam(), appendVar(), makeVar(), newVar(), copyVar(), deleteVar(), panicVar(),
		recoverVar(), printVar(), minMaxVar(), closeVar(), clearVar(), intVar(), stringVar(), boolVar(),
		byteVar(), runeVar(), errorVar(), anyVar(), float64Var(), intLocalType(), errorLocalStructType(),
		trueLocalConst(), iotaVar(), lenCaptured(), nilPointerVar(), nilParam(),
		fieldsNamedPredeclared(), methodNamedLen(), labelsNamedPredeclared(), runeLocalType(), anyLocalType(),
		funcNameShadowedByVar(), importNameShadowed(), ownNameShadowed())
}
