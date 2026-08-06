package main

// Channel comparison is reference identity (spec §Comparison operators:
// "equal if they were created by the same call to make or if both have
// value nil"; probe p12): aliases compare equal, distinct makes do not,
// a directional conversion of the same channel stays equal, channels key
// maps by identity, and channels of channels round-trip identity.

func channelComparisonIdentity() int {
	a := make(chan int)
	b := make(chan int)
	c := a
	var n chan int
	score := 0
	if a == c {
		score += 1000
	}
	if a == b {
		score += 100
	}
	if n == nil {
		score += 10
	}
	if a == nil {
		score += 1
	}
	return score
}

func channelDirectionalEqual() int {
	c := make(chan int, 1)
	var r <-chan int = c
	var s chan<- int = c
	score := 0
	if r == c {
		score += 10
	}
	if s == c {
		score += 1
	}
	return score
}

func channelOfChanIdentity() int {
	cc := make(chan chan int, 1)
	inner := make(chan int, 1)
	cc <- inner
	got := <-cc
	if got == inner {
		return 1
	}
	return 0
}

func channelMapKeyAlias() int {
	ch1 := make(chan int)
	ch2 := make(chan int)
	m := map[chan int]int{ch1: 3, ch2: 5}
	c := ch1
	return len(m)*100 + m[c]*10 + m[ch2]
}

func main() {
	channelComparisonIdentity()
}
