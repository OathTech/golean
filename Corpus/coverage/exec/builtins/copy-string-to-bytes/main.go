package main

func builtinCopyStringToBytes() int {
	dst := []byte{0, 0, 0}
	n := copy(dst, "go")
	return n*10000 + int(dst[0])*100 + int(dst[1])
}

func main() {
	builtinCopyStringToBytes()
}
