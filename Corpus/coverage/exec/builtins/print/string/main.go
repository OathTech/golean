package main

// println/print of strings — gc's printstring writes the bytes VERBATIM (no
// quoting, no escaping): empty strings, embedded separators and newlines,
// multi-byte UTF-8, a defined string type.
type Name string

func printStrings() int {
	println("hello", "", "with space", "tab\tnew\nline", "ütf8 ✓ 日本")
	print("raw", "", "concat", "\n")
	println(Name("named"), "a"+"b", string(rune(0x1F600)))
	return 0
}
