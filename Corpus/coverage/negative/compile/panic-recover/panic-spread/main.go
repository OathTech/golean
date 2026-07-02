package main

func main() {
	xs := []any{"boom"}
	panic(xs...)
}

