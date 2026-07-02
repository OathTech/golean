package main

type impossibleGeneric interface {
	int
	string
}

func requireImpossible[T impossibleGeneric](x T) {
}

func main() {
	requireImpossible(1)
}
