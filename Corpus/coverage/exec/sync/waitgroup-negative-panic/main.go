package main

import "sync"

// Driving the counter negative panics with gc's fixed message (probe
// p04): "sync: negative WaitGroup counter" — a recoverable panic()
// (the recover discriminator lives in waitgroup-basic), left
// unrecovered here so the differential pins the message.
func negativeCounter() int {
	var wg sync.WaitGroup
	wg.Add(1)
	wg.Done()
	wg.Done()
	return 0
}

func main() {
	negativeCounter()
}
