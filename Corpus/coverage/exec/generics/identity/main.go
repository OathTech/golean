package main

func id[T any](x T) T {
	return x
}

func genericIdentity() int {
	return id[int](40) + len(id[string]("go"))
}

func main() {
	genericIdentity()
}
