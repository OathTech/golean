package main

// RACY-NEGATIVE lane (channels arc slice 3, D2+D3(b); validation note
// lane d): every subject has a DATA RACE on every interleaving — the
// conflicting accesses are unordered by happens-before no matter how
// the scheduler picks — so the machine must refuse (raceDetected) on
// every tested stream, and `go run -race` is the justifying second
// oracle (TSan: no false positives; a red report is a real race).
// These cases are NEVER combined with deadlock expectations (the -race
// runtime suppresses the deadlock detector — ground-truth note §5).

// Write/write: main's x = 2 is sequenced before its receive, the
// child's x = 1 before its send — the two writes are HB-unordered on
// every schedule.
func raceWriteWrite() int {
	x := 0
	done := make(chan int)
	go func() {
		x = 1
		done <- 0
	}()
	x = 2
	<-done
	return x
}

// Read/write: main reads x concurrently with the child's write.
func raceReadWrite() int {
	x := 5
	done := make(chan int)
	go func() {
		x = 7
		done <- 0
	}()
	y := x
	<-done
	return y + x
}

// The classic unsynchronized counter: both sides read-modify-write.
func raceIncrement() int {
	x := 0
	done := make(chan int)
	go func() {
		x = x + 1
		done <- 0
	}()
	x = x + 1
	<-done
	return x
}

// Concurrent map read and map write: the map object is one location
// for race purposes (matches gc/TSan's classification).
func raceMapRW() int {
	m := map[int]int{1: 10}
	done := make(chan int)
	go func() {
		m[2] = 20
		done <- 0
	}()
	v := m[1]
	<-done
	return v
}

// Same slice ELEMENT written by both goroutines (the disjoint-element
// contrast case is race/free/slice-disjoint).
func raceSliceElem() int {
	s := make([]int, 2)
	done := make(chan int)
	go func() {
		s[0] = 1
		done <- 0
	}()
	s[0] = 2
	<-done
	return s[0] + s[1]
}

func main() {
	println(raceWriteWrite())
	println(raceReadWrite())
	println(raceIncrement())
	println(raceMapRW())
	println(raceSliceElem())
}
