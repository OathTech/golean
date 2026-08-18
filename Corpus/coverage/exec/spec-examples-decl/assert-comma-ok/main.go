package main

// spec#Type_assertions block Type_assertions-3-4a92a9bb: a type assertion in
// a two-value form yields (value, ok) with no panic on failure — in all the
// declared forms, including var v, ok interface{} = x.(T), where v and ok
// are interface{} variables whose DYNAMIC types are then T and bool.

func assertCommaOk() int {
	var x interface{} = 4
	var v int
	var ok bool
	v, ok = x.(int)
	v2, ok2 := x.(int)
	s3, ok3 := x.(string)             // fails: "", false — no panic
	var v4, ok4 interface{} = x.(int) // dynamic types of v4 and ok4 are int and bool
	n := 0
	if ok {
		n++
	}
	if ok2 {
		n++
	}
	if ok3 || s3 != "" {
		n = -100
	}
	if i, isInt := v4.(int); isInt {
		n += i // 4: v4's dynamic type is int
	}
	if b, isBool := ok4.(bool); isBool && b {
		n++ // ok4's dynamic type is bool
	}
	return v*1000 + v2*100 + n // 4407
}
