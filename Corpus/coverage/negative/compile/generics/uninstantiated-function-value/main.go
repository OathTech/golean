package main

func genericIdentityValue[T any](x T) T {
	return x
}

var _ = genericIdentityValue
