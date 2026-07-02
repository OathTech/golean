package main

func builtinAppendStringToBytes() int {
	b := append([]byte{'g'}, "o!"...)
	return len(b)*100000 + int(b[0])*1000 + int(b[1])*10 + int(b[2])
}

func main() {
	builtinAppendStringToBytes()
}
