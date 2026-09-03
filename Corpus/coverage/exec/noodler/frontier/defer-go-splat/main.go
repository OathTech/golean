// noodler frontier probe — defer f(g()) with a multi-value g (and the go-statement sibling)
package main

import "sync"

func pair() (int, int) { return 2, 3 }

var got int
var mu sync.Mutex

func record(a, b int) {
	mu.Lock()
	got = got*10 + a*b
	mu.Unlock()
}

// defer f(g()) and go f(g()) with a multi-value g.
func deferGoSplat() int {
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		record(pair())
	}()
	wg.Wait()
	func() {
		defer record(pair())
	}()
	return got
}

func main() {}
