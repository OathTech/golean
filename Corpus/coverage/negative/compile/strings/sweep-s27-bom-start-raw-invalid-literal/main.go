package main

// S27 probe A7.1: the file starts with a UTF-8 BOM (gc skips it).

func bomAtStart() (int, string) {
	s := "bomÿ"
	return len(s), s
}

func main() {
	bomAtStart()
}
