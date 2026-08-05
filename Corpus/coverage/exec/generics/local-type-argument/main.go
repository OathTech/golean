package main

func ltaId[T any](x T) T {
	return x
}

func genericLocalTypeArgument() int {
	type score int
	return int(ltaId(score(4)))
}

func main() {
	genericLocalTypeArgument()
}
