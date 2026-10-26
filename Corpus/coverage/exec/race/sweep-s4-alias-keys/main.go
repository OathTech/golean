package main

// S4 sweep (lane sweep/s4-identity, 2026-10-26): BUG-111's shape — the
// detector keys ONE word under two spellings canonically — at the routes
// born after its rows: the WHOLE-STRUCT store through a converted pointer
// (BUG-134's `Mem.storeThrough`, 2026-10-26) against a field read through
// the original, the whole-struct READ through the converted pointer against
// a field write through the original (both races: gc -race reports, the
// machine refuses on every enumerated path), the same store join-ordered
// (race-free on both sides: the confluent control), and the CHANNEL OBJECT
// reached under two spellings (`close` through the alias against a send
// through the original: the `.chanObj` key is the channel cell's root, so
// canonical by construction; gc -race reports it on every schedule). The
// send runs under `recover`: on gc's close-first schedule the send on the
// closed channel panics AFTER the detector's entry read has been recorded,
// and an unrecovered panic would be a crash report the racy lane's oracle
// refuses (measured: the bare send was green on one full run and
// `go-observation` on the next). Probed first on both sides (.tmp/probes/
// rk-*; coverage-observations --expect-status over every schedule against
// go run -race, eight gc runs of the recovered shape all RACE, no panic).

type rA struct {
	X int `json:"a"`
	Y int `json:"a"`
}
type rB struct {
	X int `json:"b"`
	Y int `json:"b"`
}
type cA struct {
	C chan int `json:"a"`
}
type cB struct {
	C chan int `json:"b"`
}

func raceWholeStoreVsFieldRead() int {
	a := rA{1, 2}
	pb := (*rB)(&a)
	done := make(chan int)
	go func() {
		*pb = rB{8, 9}
		done <- 0
	}()
	v := a.Y
	<-done
	return v + a.X
}

func raceWholeReadVsFieldWrite() int {
	a := rA{1, 2}
	pb := (*rB)(&a)
	done := make(chan int)
	go func() {
		a.Y = 5
		done <- 0
	}()
	v := *pb
	<-done
	return v.X + a.Y
}

func freeWholeStoreJoined() int {
	a := rA{1, 2}
	pb := (*rB)(&a)
	done := make(chan int)
	go func() {
		*pb = rB{8, 9}
		done <- 0
	}()
	<-done
	v := *pb
	return a.Y*10 + v.X
}

func trySend(c chan int) (sent int) {
	defer func() {
		if recover() != nil {
			sent = 2
		}
	}()
	c <- 1
	return 1
}

func raceChanViaAlias() int {
	a := cA{make(chan int, 1)}
	pb := (*cB)(&a)
	done := make(chan int)
	go func() {
		close(pb.C)
		done <- 0
	}()
	v := trySend(a.C)
	<-done
	return v
}

func main() {
	println(freeWholeStoreJoined())
}
