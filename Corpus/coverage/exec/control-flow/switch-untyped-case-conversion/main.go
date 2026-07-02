package main

type switchSmallInt int8

func switchUntypedCaseConversion() int {
	var x switchSmallInt = 2
	switch x {
	case 1 + 1:
		return 1
	default:
		return 0
	}
}

