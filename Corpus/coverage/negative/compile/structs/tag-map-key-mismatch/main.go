package main

func main() {
	m := map[struct {
		X int `tag:"a"`
	}]int{}
	var k struct {
		X int `tag:"b"`
	}
	_ = m[k]
}
