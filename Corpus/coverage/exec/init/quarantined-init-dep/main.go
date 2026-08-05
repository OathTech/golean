package main

func quarantinedInitHelper() int {
	ch := make(chan int, 1)
	ch <- 4
	return <-ch
}

var quarantinedInitVal = quarantinedInitHelper()

func quarantinedInitDep() int {
	return quarantinedInitVal * 10
}

func main() {
	quarantinedInitDep()
}
