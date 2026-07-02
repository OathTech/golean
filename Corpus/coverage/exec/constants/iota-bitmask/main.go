package main

const (
	iotaRead = 1 << iota
	iotaWrite
	iotaExec
	iotaAll = iotaRead | iotaWrite | iotaExec
)

func iotaBitmask() int {
	return iotaRead*1000 + iotaWrite*100 + iotaExec*10 + iotaAll
}
