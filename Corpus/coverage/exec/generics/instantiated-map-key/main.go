package main

type keyPair[A comparable, B comparable] struct {
	a A
	b B
}

func keyMake[A comparable, B comparable](a A, b B) keyPair[A, B] {
	return keyPair[A, B]{a: a, b: b}
}

func genericInstantiatedMapKey() int {
	m := map[keyPair[int, string]]int{}
	m[keyMake(1, "a")] = 10
	m[keyMake(2, "b")] = 20
	m[keyPair[int, string]{a: 1, b: "a"}] = 11
	return len(m)*100 + m[keyMake(1, "a")]
}

func main() {
	genericInstantiatedMapKey()
}
