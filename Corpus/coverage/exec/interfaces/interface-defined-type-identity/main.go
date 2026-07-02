package main

type identityDefinedA int
type identityDefinedB int

func interfaceDefinedTypeIdentity() int {
	var a any = identityDefinedA(3)
	var b any = identityDefinedB(3)
	var c any = identityDefinedA(3)
	score := 0
	if a == b {
		score += 1
	}
	if a == c {
		score += 10
	}
	return score
}
