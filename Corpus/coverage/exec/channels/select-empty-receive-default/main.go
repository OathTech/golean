package main

func channelSelectEmptyReceiveDefault() int {
	ch := make(chan int, 1)
	picked := 0
	v := 0
	select {
	case v = <-ch:
		picked = 1
	default:
		picked = 2
	}
	return picked*100 + len(ch)*10 + v
}
