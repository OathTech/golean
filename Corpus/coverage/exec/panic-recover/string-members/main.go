package main

// This whole subject package stays inside the explicit-string recovery
// profile. Broader dynamic-kind/byte controls live in a separate package
// that includes this file byte-for-byte.
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

func main() {}
