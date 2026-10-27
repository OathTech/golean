package main

type box[T any] struct{ v T }

func (b box[int]) Get() int { return 0 } // the receiver DECLARES a type parameter named int: 0 is not assignable to it

func main() {}
