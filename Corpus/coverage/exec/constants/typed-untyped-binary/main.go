package main

type typedUntypedInt int

func typedUntypedBinaryConstant() int {
	const base typedUntypedInt = 7
	var x typedUntypedInt = base + 5
	return int(x)
}
