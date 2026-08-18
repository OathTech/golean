package main

// spec#Constant_expressions block Constant_expressions-3-8a328e0d: constant
// expressions are computed exactly — Huge == 1 << 100 exists as an untyped
// integer constant far beyond any machine width, and Four int8 = Huge >> 98
// == 4 is representable and typed int8.

const Huge = 1 << 100 // untyped integer constant

const Four int8 = Huge >> 98 // Four == 4 (type int8)

func constHugeShift() int {
	var f8 int8 = Four
	if Huge>>99 != 2 { // more exact arithmetic over the huge constant
		return -1
	}
	return int(f8) // 4
}
