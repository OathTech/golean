package main

// spec#Type_switches block Type_switches-4-595985f9: the spec's
// hand-translation of its type switch into an if/type-assertion
// chain — "the type switch of the previous example could be rewritten
// as". Pins the stated equivalence: v := x evaluates x exactly once;
// nil is tested with v == nil; each single-type case becomes
// i, isT := v.(T); the (bool, string) list and default become
// assertion-ok fan-outs where i := v keeps x's interface type.
// Adaptation: print* helpers become returned labels/details, and the
// spec's unused `i := v` bindings get `_ = i` (verbatim they would be
// "declared and not used" — noted; the binding itself is the point).
// Expected: identical (label, detail) to the type-switch form for
// every selector, and the agree subject returns true for all.

func tseValue(sel int) interface{} {
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

func tseSwitchForm(x interface{}) (string, float64) {
	label := ""
	detail := 0.0
	switch i := x.(type) {
	case nil:
		label = "x is nil"
	case int:
		label = "int"
		detail = float64(i)
	case float64:
		label = "float64"
		detail = i
	case func(int) float64:
		label = "func"
		detail = i(4)
	case bool, string:
		label = "type is bool or string"
	default:
		label = "don't know the type"
	}
	return label, detail
}

func tseIfChainForm(x interface{}) (string, float64) {
	label := ""
	detail := 0.0
	v := x // x is evaluated exactly once
	if v == nil {
		i := v // type of i is type of x (interface{})
		_ = i
		label = "x is nil"
	} else if i, isInt := v.(int); isInt {
		label = "int" // type of i is int
		detail = float64(i)
	} else if i, isFloat64 := v.(float64); isFloat64 {
		label = "float64" // type of i is float64
		detail = i
	} else if i, isFunc := v.(func(int) float64); isFunc {
		label = "func" // type of i is func(int) float64
		detail = i(4)
	} else {
		_, isBool := v.(bool)
		_, isString := v.(string)
		if isBool || isString {
			i := v // type of i is type of x (interface{})
			_ = i
			label = "type is bool or string"
		} else {
			i := v // type of i is type of x (interface{})
			_ = i
			label = "don't know the type"
		}
	}
	return label, detail
}

func typeSwitchIfChain(sel int) (string, float64) {
	return tseIfChainForm(tseValue(sel))
}

func typeSwitchFormsAgree(sel int) bool {
	x := tseValue(sel)
	l1, d1 := tseSwitchForm(x)
	l2, d2 := tseIfChainForm(x)
	return l1 == l2 && d1 == d2
}

func main() {
	typeSwitchFormsAgree(2)
}
