package main

func f() struct {
	X int `tag:"a"`
} {
	return struct {
		X int `tag:"b"`
	}{X: 1}
}

func main() {
	_ = f()
}
