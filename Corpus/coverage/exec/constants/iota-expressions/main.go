package main

const (
	_  = iota
	KB = 1 << (10 * iota)
	MB
	GB
)

func iotaExpressions() int {
	return KB/1024 + MB/(1024*1024)*10 + GB/(1024*1024*1024)*100
}
