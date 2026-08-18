package main

// spec#Type_switches block Type_switches-5-0b078ebe: a type switch may use a
// TYPE PARAMETER in its cases — for f[string], case P duplicates case string
// and the FIRST matching case wins (v1 == 0, not 1); for f[byte], []byte
// matches case []P first (v2 == 2). An extra probe hits default (nothing
// matches float64 for f[string]).

func f[P any](x any) int {
	switch x.(type) {
	case P:
		return 0
	case string:
		return 1
	case []P:
		return 2
	case []byte:
		return 3
	default:
		return 4
	}
}

var v1 = f[string]("foo")  // v1 == 0
var v2 = f[byte]([]byte{}) // v2 == 2

func genericTypeSwitch() int {
	return v1*100 + v2*10 + f[string](3.5) // 024 = 24
}
