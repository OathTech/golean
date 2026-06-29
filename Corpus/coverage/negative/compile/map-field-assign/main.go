package main

type counter struct {
	n int
}

func main() {
	m := map[string]counter{"a": {n: 1}}
	m["a"].n = 2
}
