package main

// Worker pools with ORDER-INDEPENDENT aggregation: which worker's
// partial lands first is scheduling latitude, but the fold is
// commutative — the aggregate is confluent and strict-lane testable.

func workerPoolSum() int {
	results := make(chan int, 3)
	for w := 1; w <= 3; w++ {
		go func(base int) {
			sum := 0
			for i := 0; i < 4; i++ {
				sum += base*10 + i
			}
			results <- sum
		}(w)
	}
	total := 0
	for i := 0; i < 3; i++ {
		total += <-results
	}
	return total
}

func workerPoolSharedFeed() int {
	work := make(chan int, 6)
	results := make(chan int, 2)
	for i := 1; i <= 6; i++ {
		work <- i
	}
	close(work)
	for w := 0; w < 2; w++ {
		go func() {
			sum := 0
			for v := range work {
				sum += v * v
			}
			results <- sum
		}()
	}
	// Which worker drains which item is latitude; the sum of squares
	// 1..6 is not.
	return <-results + <-results
}

func main() {
	workerPoolSum()
	workerPoolSharedFeed()
}
