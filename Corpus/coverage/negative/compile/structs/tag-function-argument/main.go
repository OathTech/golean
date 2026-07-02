package main

func takesTagged(struct {
	X int `tag:"a"`
}) {
}

func main() {
	var x struct {
		X int `tag:"b"`
	}
	takesTagged(x)
}
