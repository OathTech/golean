package main

// spec#Type_switches block Type_switches-3-8bc27ecc: the spec's type
// switch over an interface{} x — a nil case selected when x is a nil
// interface value; single-type cases in which i has that case's type;
// a multi-type case (bool, string) and default in which i has x's own
// interface type. Adaptation: the print* helpers become returned
// labels (and a numeric detail proving i's typed value is usable:
// the int case returns i itself, the float64 case i, the func case
// i(4)). Expected by selector:
//   0 (nil interface)      -> "x is nil", 0
//   1 (int 7)              -> "int", 7
//   2 (float64 2.5)        -> "float64", 2.5
//   3 (func(int) float64)  -> "func", 6 (the func returns n*1.5)
//   4 (bool), 5 (string)   -> "type is bool or string", 0
//   6 (int32 9)            -> "don't know the type", 0

func tsValue(sel int) interface{} {
	switch sel {
	case 0:
		return nil
	case 1:
		return 7
	case 2:
		return 2.5
	case 3:
		return func(n int) float64 { return float64(n) * 1.5 }
	case 4:
		return true
	case 5:
		return "str"
	default:
		return int32(9)
	}
}

func typeSwitchSpec(sel int) (string, float64) {
	x := tsValue(sel)
	label := ""
	detail := 0.0
	switch i := x.(type) {
	case nil:
		label = "x is nil" // type of i is type of x (interface{})
	case int:
		label = "int" // type of i is int
		detail = float64(i)
	case float64:
		label = "float64" // type of i is float64
		detail = i
	case func(int) float64:
		label = "func" // type of i is func(int) float64
		detail = i(4)
	case bool, string:
		label = "type is bool or string" // type of i is type of x (interface{})
	default:
		label = "don't know the type" // type of i is type of x (interface{})
	}
	return label, detail
}

func main() {
	typeSwitchSpec(1)
}
