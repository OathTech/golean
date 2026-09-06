package main

// Auxiliary explicit-literal family for the broader historical controls.
// The original historical subject is the byte-identical main.go; this
// control package is not advertised as admitted by the O2 profile.
func equalHandler() {
	_ = recover()
	panic("orig")
}

func unequalHandler() {
	_ = recover()
	panic("next")
}

func thirdHandler() {
	_ = recover()
	panic("third")
}

func Equal() {
	defer equalHandler()
	panic("orig")
}

func Unequal() {
	defer unequalHandler()
	panic("orig")
}

func Multiple() {
	defer thirdHandler()
	defer equalHandler()
	panic("orig")
}

func InvalidBefore() {
	panic("\xff\x00\\\nZ")
}

func InvalidAfter() {
	panic("a\n\xff")
}

func InvalidRecovered() {
	defer equalHandler()
	panic("\xff\x00\\\nZ")
}

func Unicode() {
	panic("界🙂")
}

func Controls() {
	panic("a\x00\x01\t\r\nZ")
}

func Normal() bool {
	return true
}

// The original historical main lives in the byte-identical main.go.
