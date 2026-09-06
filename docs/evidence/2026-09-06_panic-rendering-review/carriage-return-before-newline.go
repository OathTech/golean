package main
func main(){ defer func(){ recover(); panic("other") }(); panic(string([]byte{97,13,10,98})) }
