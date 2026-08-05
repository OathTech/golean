package main

func derivedInner[U any](u U) U {
	return u
}

func derivedLen[T any](xs []T) int {
	return len(derivedInner(xs))
}

func derivedOuter[T any](x T) int {
	pair := derivedInner([]T{x, x})
	return len(pair) * derivedLen([]T{x, x, x})
}

func genericDerivedInstantiation() int {
	return derivedOuter(2)*100 + derivedOuter("s")
}

func main() {
	genericDerivedInstantiation()
}
