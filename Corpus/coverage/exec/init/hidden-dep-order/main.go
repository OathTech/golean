package main

type hiddenI interface{ ab() int }

type hiddenT struct{}

func (hiddenT) ab() int { return hiddenA*10 + hiddenB }

var hiddenX = hiddenI(hiddenT{}).ab() // hidden dependency on hiddenA, hiddenB
var hiddenA = hiddenB
var hiddenB = 42

func hiddenDepOrder() int {
	return hiddenX*10000 + hiddenA*100 + hiddenB
}

func main() {
	hiddenDepOrder()
}
