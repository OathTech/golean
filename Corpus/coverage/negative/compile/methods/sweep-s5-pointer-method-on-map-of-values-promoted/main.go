package main

type inner struct{ n int }

func (i *inner) inc() { i.n++ }

type outer struct{ inner }

func main() {
	m := map[string]outer{"k": {}}
	m["k"].inc() // a promoted pointer method on a map element
}
