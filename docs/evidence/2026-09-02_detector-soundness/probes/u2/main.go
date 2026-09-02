package main

// Detector-soundness probes, U2 family (Race.lean inventory: `len`/`cap` on
// CHANNELS record nothing — spec: channels need no further synchronization;
// gc's chanlen/chancap read c.qcount/c.dataqsiz uninstrumented, probe p26).
// Each subject puts a len/cap read beside a concurrent op on the same object
// and lets the two oracles (go run -race, the machine's enumerator) grade it.
// Expected cells are stated per subject; the runner records what happened.

// U2-1: len(ch) beside a concurrent send. Expect agree-DRF (uninstrumented
// on both sides; n ∈ {0,1} is scheduling latitude, not a race).
func u2LenChanVsSend() int {
	ch := make(chan int, 2)
	done := make(chan int)
	go func() {
		ch <- 1
		done <- 0
	}()
	n := len(ch)
	<-done
	return n
}

// U2-2: cap(ch) beside a concurrent close. Expect agree-DRF.
func u2CapChanVsClose() int {
	ch := make(chan int, 3)
	done := make(chan int)
	go func() {
		close(ch)
		done <- 0
	}()
	c := cap(ch)
	<-done
	return c
}

// U2-3 CONTROL: len(m) on a MAP beside a concurrent map write — recorded
// (S3 audit refuted "len is uninstrumented" for maps; the corpus pin is
// race/negative/len-map). Expect agree-race.
func u2LenMapVsWrite() int {
	m := map[int]int{}
	done := make(chan int)
	go func() {
		m[1] = 1
		done <- 0
	}()
	n := len(m)
	<-done
	return n
}

// U2-4: len(s) on a SLICE variable beside a concurrent append-reassignment.
// The len reads the header VARIABLE s (gc: instrumented read of s; machine:
// the evalVar read of s's cell) against the storeK write. Expect agree-race.
func u2LenSliceVarVsAppend() int {
	s := make([]int, 1, 4)
	done := make(chan int)
	go func() {
		s = append(s, 2)
		done <- 0
	}()
	n := len(s)
	<-done
	return n
}

// U2-5: len(a) on an ARRAY variable beside a concurrent element write. len of
// an array is a compile-time constant (spec §Length and capacity) — gc reads
// nothing; the frontend must constant-fold it too, else the evalVar whole-
// cell read over-refuses. Expect agree-DRF.
func u2LenArrayVsElemWrite() int {
	var a [3]int
	done := make(chan int)
	go func() {
		a[0] = 5
		done <- 0
	}()
	n := len(a)
	<-done
	return n + a[0]
}

// U2-6: len(str) beside a concurrent string-variable write. Expect agree-race
// (header read vs header write).
func u2LenStringVsWrite() int {
	s := "ab"
	done := make(chan int)
	go func() {
		s = "xyz"
		done <- 0
	}()
	n := len(s)
	<-done
	return n
}

// U2-7: cap(s) on a slice variable beside a concurrent reslice-reassignment.
// Expect agree-race.
func u2CapSliceVarVsReslice() int {
	s := make([]int, 2, 4)
	done := make(chan int)
	go func() {
		s = s[:1]
		done <- 0
	}()
	c := cap(s)
	<-done
	return c
}

func main() {
	println(u2LenChanVsSend(), u2CapChanVsClose(), u2LenMapVsWrite(), u2LenSliceVarVsAppend(),
		u2LenArrayVsElemWrite(), u2LenStringVsWrite(), u2CapSliceVarVsReslice())
}
