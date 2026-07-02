package main

type typedConstantString string

func typedStringBinaryConstant() int {
	const prefix typedConstantString = "go"
	const whole = prefix + "lean"
	var s typedConstantString = whole
	return len(s)*1000 + int(s[2])
}
