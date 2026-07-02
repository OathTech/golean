package main

type byteBag []byte

func builtinAppendDefinedByteSliceString() int {
	var b byteBag = byteBag{'a'}
	b = append(b, "bc"...)
	return len(b)*100000 + int(b[0])*1000 + int(b[1])*10 + int(b[2])
}

func main() {
	builtinAppendDefinedByteSliceString()
}
