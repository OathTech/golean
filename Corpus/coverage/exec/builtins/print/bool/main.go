package main

// println/print of bools — gc's printbool (`true`/`false`); a defined bool
// type prints as its underlying kind.
type Flag bool

func printBools() int {
	println(true, false)
	print(true, false, "\n")
	println(Flag(true), 1 < 2, 2 < 1)
	return 0
}
