package main

// spec#An_example_package block An_example_package-1-d5a327de: the
// spec's complete example program — the concurrent prime sieve.
// generate feeds 2, 3, 4, ... into a channel; each filter goroutine
// passes along only the values not divisible by its prime; sieve
// daisy-chains a new filter for each prime received, so the values
// arriving at the head of the chain are exactly the primes in order.
// Adaptation: the spec's sieve() prints forever; here it collects the
// first k primes and returns (fmt.Print replaced by accumulation into
// the result — subjects must not print). The generate/filter chain is
// otherwise verbatim; the leftover goroutines are left parked on
// their sends when the subject returns, like the spec program's would
// be at any point. Every observable is fixed by the synchronous
// channel chain (single consumer per channel), schedule-independent.
// Expected: first 5 primes 2, 3, 5, 7, 11, encoded acc = acc*100 + p
// -> 203050711; with k = 8 the primes run through 19 and the same
// encoding gives 203050711131719.

// Send the sequence 2, 3, 4, ... to channel 'ch'.
func psGenerate(ch chan<- int) {
	for i := 2; ; i++ {
		ch <- i // Send 'i' to channel 'ch'.
	}
}

// Copy the values from channel 'src' to channel 'dst',
// removing those divisible by 'prime'.
func psFilter(src <-chan int, dst chan<- int, prime int) {
	for i := range src { // Loop over values received from 'src'.
		if i%prime != 0 {
			dst <- i // Send 'i' to channel 'dst'.
		}
	}
}

// The prime sieve: Daisy-chain filter processes together.
func primeSieveFirst(k int) int {
	acc := 0
	ch := make(chan int) // Create a new channel.
	go psGenerate(ch)    // Start generate() as a subprocess.
	for n := 0; n < k; n++ {
		prime := <-ch
		acc = acc*100 + prime
		ch1 := make(chan int)
		go psFilter(ch, ch1, prime)
		ch = ch1
	}
	return acc
}

func main() {
	primeSieveFirst(5)
}
