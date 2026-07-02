package main

func main() {
	var x struct {
		X int `tag:"a"`
	}
	var y struct {
		X int `tag:"b"`
	}
	x = y
}
