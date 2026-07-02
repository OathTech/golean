package main

type box[T any] struct {
	value T
}

func genericStruct() int {
	i := box[int]{value: 7}
	s := box[string]{value: "go"}
	return i.value*10 + len(s.value)
}

func main() {
	genericStruct()
}
