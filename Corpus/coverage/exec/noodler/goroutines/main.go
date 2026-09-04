// noodler probes — goroutine programs whose outcome the memory model
// FORCES (mem#chan, mem#locks, mem#once): every row is strict; a
// machine that admitted a second outcome would fail at stage nondet.
package main

import "sync"

// Write before send; receive before read: forced 1.
func handoffWriteBeforeSend() int {
	x := 0
	ch := make(chan struct{})
	go func() {
		x = 1
		ch <- struct{}{}
	}()
	<-ch
	return x
}

// Sends from one goroutine arrive in order.
func fifoFromOneSender() int {
	ch := make(chan int)
	go func() {
		for i := 1; i <= 4; i++ {
			ch <- i
		}
		close(ch)
	}()
	r := 0
	for v := range ch {
		r = r*10 + v
	}
	return r
}

// Close broadcasts: three receivers each observe zero,false.
func closeBroadcast() int {
	ch := make(chan int)
	var wg sync.WaitGroup
	var mu sync.Mutex
	zeros, falses := 0, 0
	for i := 0; i < 3; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			v, ok := <-ch
			mu.Lock()
			if v == 0 {
				zeros++
			}
			if !ok {
				falses++
			}
			mu.Unlock()
		}()
	}
	close(ch)
	wg.Wait()
	return zeros*10 + falses
}

// Worker pool: the sum of results is order-independent.
func workerPoolSum() int {
	jobs := make(chan int, 9)
	results := make(chan int, 9)
	var wg sync.WaitGroup
	for w := 0; w < 3; w++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for j := range jobs {
				results <- j * j
			}
		}()
	}
	for i := 1; i <= 9; i++ {
		jobs <- i
	}
	close(jobs)
	wg.Wait()
	close(results)
	sum := 0
	for r := range results {
		sum += r
	}
	return sum
}

// sync.Once runs exactly once across goroutines.
func onceAcrossGoroutines() int {
	var once sync.Once
	var wg sync.WaitGroup
	var mu sync.Mutex
	count := 0
	for i := 0; i < 5; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			once.Do(func() {
				mu.Lock()
				count++
				mu.Unlock()
			})
		}()
	}
	wg.Wait()
	return count
}

// Mutex-protected counter: 2 x 50 increments.
func mutexCounter() int {
	var mu sync.Mutex
	var wg sync.WaitGroup
	n := 0
	for g := 0; g < 2; g++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for i := 0; i < 50; i++ {
				mu.Lock()
				n++
				mu.Unlock()
			}
		}()
	}
	wg.Wait()
	return n
}

// RWMutex: a writer publishes, readers (after a channel signal) all see
// the value.
func rwMutexReaders() int {
	var rw sync.RWMutex
	var wg sync.WaitGroup
	var mu sync.Mutex
	v := 0
	written := make(chan struct{})
	go func() {
		rw.Lock()
		v = 7
		rw.Unlock()
		close(written)
	}()
	<-written
	sum := 0
	for i := 0; i < 3; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			rw.RLock()
			x := v
			rw.RUnlock()
			mu.Lock()
			sum += x
			mu.Unlock()
		}()
	}
	wg.Wait()
	return sum
}

// WaitGroup counter blocked forever: deadlock.
func waitGroupDeadlock() int {
	var wg sync.WaitGroup
	wg.Add(1)
	wg.Wait()
	return 1
}

// Double lock in the only goroutine: deadlock.
func mutexDoubleLockDeadlock() int {
	var mu sync.Mutex
	mu.Lock()
	mu.Lock()
	return 1
}

// A goroutine still blocked when main returns is fine.
func leakedGoroutineOnReturn() int {
	ch := make(chan int)
	go func() { <-ch }()
	return 1
}

// Directional channel parameters.
func producer(out chan<- int, n int) {
	for i := 1; i <= n; i++ {
		out <- i
	}
	close(out)
}

func consumer(in <-chan int) int {
	s := 0
	for v := range in {
		s += v
	}
	return s
}

func directionalParams() int {
	ch := make(chan int)
	go producer(ch, 5)
	return consumer(ch)
}

// Pipeline of three stages.
func pipelineThreeStages() int {
	gen := func(n int) <-chan int {
		out := make(chan int)
		go func() {
			for i := 1; i <= n; i++ {
				out <- i
			}
			close(out)
		}()
		return out
	}
	sq := func(in <-chan int) <-chan int {
		out := make(chan int)
		go func() {
			for v := range in {
				out <- v * v
			}
			close(out)
		}()
		return out
	}
	total := 0
	for v := range sq(sq(gen(3))) {
		total += v
	}
	return total
}

// Buffered channel used as a counting semaphore; the total work is
// forced.
func semaphoreTotal() int {
	sem := make(chan struct{}, 2)
	var wg sync.WaitGroup
	var mu sync.Mutex
	total := 0
	for i := 1; i <= 6; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			sem <- struct{}{}
			mu.Lock()
			total += i
			mu.Unlock()
			<-sem
		}()
	}
	wg.Wait()
	return total
}

// Two goroutines synchronize via a pair of unbuffered channels in a
// fixed protocol; observable is the transcript.
func lockstepTranscript() int {
	a2b := make(chan int)
	b2a := make(chan int)
	go func() {
		v := <-a2b
		b2a <- v * 2
		v = <-a2b
		b2a <- v * 2
	}()
	r := 0
	a2b <- 1
	r = r*100 + <-b2a
	a2b <- 3
	r = r*100 + <-b2a
	return r
}

// Panic in a goroutine while main is blocked on WaitGroup.Wait aborts.
func goroutinePanicUnderWait() int {
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		panic("under-wait")
	}()
	wg.Wait()
	return 1
}

// The deterministic twin of goroutinePanicUnderWait: the panicking
// goroutine has NO deferred Done, so nothing ever wakes main's Wait and
// the runtime's crash on the unrecovered panic is the only way out — gc
// panics on every schedule (there is no wake for main to race). Pins the
// unrecovered-goroutine-panic-aborts-the-program behaviour without the
// schedule-dependent wake that makes the sibling a membership row.
func goroutinePanicUnderWaitNoDone() int {
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		panic("under-wait-no-done")
	}()
	wg.Wait()
	return 1
}

// nil channel send in a child never completes; main still returns.
func childBlockedOnNilChannel() int {
	var ch chan int
	go func() { ch <- 1 }()
	return 2
}

func main() {}
