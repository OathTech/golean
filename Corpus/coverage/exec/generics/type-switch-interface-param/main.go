package main

// Surfaced by the gotest triage re-run of stdlib slice 3 (2026-09-04;
// $GOROOT/test/typeparam/typeswitch3.go, its output now COMPARED): a type
// switch inside a generic function whose `case T` is the type parameter
// instantiated to an INTERFACE type J. gc matches `case T` iff the dynamic
// type implements J (myint has foo but not bar → falls to `case myint`);
// the machine matched `case T` for f[J](myint(11)). BUGS.md BUG-095.
type I interface{ foo() int }
type J interface {
	I
	bar()
}

type myint int

func (x myint) foo() int { return int(x) }

type myint32 int32

func (x myint32) foo() int { return int(x) }
func (x myint32) bar()     {}

// which reports the matched case: 1 = case T, 2 = case myint, 3 = default.
func which[T I](i I) int {
	switch i.(type) {
	case T:
		return 1
	case myint:
		return 2
	default:
		return 3
	}
}

func typeSwitchInterfaceParam() (int, int, int, int) {
	return which[J](myint(11)), which[J](myint32(12)), which[I](myint(10)), which[myint32](myint(5))
}

// whichBound is typeswitch3.go's exact shape: the switch BINDS `x := i.(type)`
// and the arm calls a method on the bound value.
func whichBound[T I](i I) int {
	switch x := i.(type) {
	case T:
		return 100 + x.foo()
	case myint:
		return 200 + x.foo()
	default:
		return 300 + x.foo()
	}
}

func typeSwitchInterfaceParamBound() (int, int, int, int) {
	return whichBound[J](myint(11)), whichBound[J](myint32(12)), whichBound[I](myint(10)), whichBound[myint32](myint(5))
}

// whichPlain: the NON-generic twin — `case J` spelled directly. Separates
// "interface embedding in a type-switch case" from "type parameter
// instantiated to an interface".
func whichPlain(i I) int {
	switch i.(type) {
	case J:
		return 1
	case myint:
		return 2
	default:
		return 3
	}
}

func typeSwitchInterfacePlain() (int, int) {
	return whichPlain(myint(11)), whichPlain(myint32(12))
}
