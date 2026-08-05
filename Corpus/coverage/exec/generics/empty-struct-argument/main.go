package main

func esId[T any](x T) T {
	return x
}

func genericEmptyStructArgument() int {
	v := esId(struct{}{})
	if v == (struct{}{}) {
		return 8
	}
	return -1
}

func main() {
	genericEmptyStructArgument()
}
