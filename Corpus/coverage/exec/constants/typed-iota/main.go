package main

const (
	typedIotaA byte = iota
	typedIotaB
	typedIotaC
)

func typedIota() int {
	return int(typedIotaA)*100 + int(typedIotaB)*10 + int(typedIotaC)
}
