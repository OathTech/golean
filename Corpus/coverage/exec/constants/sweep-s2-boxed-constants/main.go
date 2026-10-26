package main

// Defect-neighbourhood campaign, shape S2 (conversions: a missing kernel arm or a
// value not retagged), lane sweep/s2-conversions, 2026-10-26: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// Constant conversions fold through emitConstValue with their UNDERLYING kind;
// the defined type must still reach the box (the dynamic type).

type MyInt int
type MyStr string
type MyFloat float64
type MyBool2 bool

func kind(i any) int {
	switch i.(type) {
	case int:
		return 1
	case MyInt:
		return 2
	case string:
		return 3
	case MyStr:
		return 4
	case float64:
		return 5
	case MyFloat:
		return 6
	case bool:
		return 7
	case MyBool2:
		return 8
	}
	return 0
}

func boxedConvertedInts() int {
	x := 5
	var a any = MyInt(x)
	var b any = int(MyInt(x))
	var c any = MyInt(3)
	var d any = int64(x)
	k := 0
	if _, ok := d.(int64); ok {
		k = 9
	}
	return kind(a)*1000 + kind(b)*100 + kind(c)*10 + k
}

func boxedConvertedString() int {
	s := "x"
	var a any = MyStr(s)
	var b any = MyStr("lit")
	var c any = string(MyStr(s))
	return kind(a)*100 + kind(b)*10 + kind(c)
}

func boxedConvertedFloat() int {
	f := 1.5
	var a any = MyFloat(f)
	var b any = MyFloat(2)
	var c any = float64(MyFloat(f))
	return kind(a)*100 + kind(b)*10 + kind(c)
}

func boxedConvertedBool() int {
	var a any = MyBool2(true)
	var b any = bool(MyBool2(false))
	return kind(a)*10 + kind(b)
}

func main() {}
