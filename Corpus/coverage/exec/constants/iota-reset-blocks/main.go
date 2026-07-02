package main

const (
	iotaResetA = iota
	iotaResetB
)

const (
	iotaResetC = iota
	iotaResetD
)

func iotaResetBlocks() int {
	return iotaResetA*1000 + iotaResetB*100 + iotaResetC*10 + iotaResetD
}
