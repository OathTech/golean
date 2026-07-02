package main

type genericHolder[T any] struct {
	v T
}

func (h genericHolder[T]) Get() T {
	return h.v
}

func genericTypeMethodDispatch() int {
	return genericHolder[int]{v: 5}.Get()*10 + len(genericHolder[string]{v: "go"}.Get())
}

func main() {
	genericTypeMethodDispatch()
}
