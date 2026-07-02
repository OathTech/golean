package main

type hasGenericM interface {
	M()
}

func requireGenericM[T hasGenericM](x T) {
}

func main() {
	requireGenericM(1)
}
