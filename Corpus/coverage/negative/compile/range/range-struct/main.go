package main

func main() {
	s := struct{ n int }{n: 1}
	for range s {
	}
}
