package main

func namedDefaults(flag bool) (x int, y string, z bool) {
	if flag {
		x = 3
	}
	return
}

func namedResultDefaults() (int, string, bool) {
	return namedDefaults(false)
}

func main() {
	namedResultDefaults()
}
