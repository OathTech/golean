package main

type genericSigned interface {
	~int | ~int8
}

type genericComparableSigned interface {
	genericSigned
	comparable
}

func sameOrAdd[T genericComparableSigned](a T, b T) int {
	if a == b {
		return int(a) * 10
	}
	return int(a) + int(b)
}

func genericConstraintEmbedding() int {
	return sameOrAdd(3, 3) + sameOrAdd(int8(2), int8(5))
}

func main() {
	genericConstraintEmbedding()
}
