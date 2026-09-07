package main

func main() {
	defer func() {
		_ = recover()
		var q *int
		_ = *q
	}()
	var p *int
	_ = *p
}
