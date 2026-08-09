package main

import "sync"

var joined int

// The mutex+WaitGroup integration shape (the parallel_search_replace
// idiom): three workers increment under the lock, main joins with
// Wait. Mutual exclusion plus the Done→Wait edges make the readout
// schedule-independent (confluent lane).
func workersJoin() int {
	joined = 0
	var m sync.Mutex
	var wg sync.WaitGroup
	for i := 0; i < 3; i++ {
		wg.Add(1)
		go func() {
			m.Lock()
			joined = joined + 1
			m.Unlock()
			wg.Done()
		}()
	}
	wg.Wait()
	return joined
}

func main() {
	workersJoin()
}
