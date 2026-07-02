package main

func mapLiteralInterfaceDistinctDynamicType() int {
	var a any = int8(1)
	var b any = int16(1)
	m := map[any]int{
		a: 7,
		b: 9,
	}
	return len(m)*100 + m[a]*10 + m[b]
}
