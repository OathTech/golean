package main

type quarantinedIface interface {
	qval() int
}

type quarantinedImpl struct{}

func (quarantinedImpl) qval() int {
	return quarantinedIfaceHelper()
}

func quarantinedIfaceHelper() int {
	ch := make(chan int, 1)
	ch <- 4
	return <-ch
}

var quarantinedIfaceVal = quarantinedIface(quarantinedImpl{}).qval()

func quarantinedInitIface() int {
	return quarantinedIfaceVal * 10
}

func main() {
	quarantinedInitIface()
}
