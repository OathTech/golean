package main

// E9 cross-goroutine delete-prune witness (Tier-5 slice, 2026-09-02;
// fidelity finding A1-20, inventory E9 REOPEN → CLOSED). Goroutine A
// (the subject) ranges over m; on its FIRST production it hands the
// produced key k to goroutine B over an unbuffered channel; B deletes
// k, re-inserts k, and acks; A continues the range. Every map access is
// HB-ordered by the req/ack handshake (DRF: `go run -race` green,
// 200/200 at the probe), so there is NO race to refuse — the shape is a
// pure envelope question.
//
// spec#For_statements (range clause, maps): "If a map entry that has
// not yet been reached is removed during iteration, the corresponding
// iteration value will not be produced. If a map entry is created
// during iteration, that entry may be produced during the iteration or
// may be skipped." Under the adopted reading I-1 (a deleted-then-
// re-created key is a NEW entry; ledger L-012, [USER] ruling
// 2026-08-19, full literal envelope) the re-created k MAY be produced
// again or MAY be skipped.
//
// BEFORE the pool-level prune (`pruneForeign`, Multi.lean) the machine
// pruned only the DELETING goroutine's in-flight frames, so A's
// produced-set still held k and re-production was unrealizable: the
// enumerated set was the singleton {3} and the membership lint refused
// the row (permitted ∉ modeled on a DRF program). With the foreign
// prune the set is {3, 4}: 3 = the re-created entry skipped, 4 = it is
// produced again. gc's plain-shape sample is 3 (160,000/160,000
// in-process trials over GOMAXPROCS ∈ {1, 8} × sizes {3, 8, 100, 1000},
// plus 600 fresh-process runs — never 4); the INSERT variant below is
// where gc exhibits the other member.
func crossGoroutineDeleteReAdd() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	req := make(chan int)
	ack := make(chan int)
	go func() {
		k := <-req
		delete(m, k)
		m[k] = k + 10
		ack <- 0
	}()
	n := 0
	first := true
	for k := range m {
		n++
		if first {
			first = false
			req <- k
			<-ack
		}
	}
	return n
}

// The INTERVENING-INSERT leg: B also inserts ONE fresh key between the
// delete and the re-insert of k, so the re-created k lands in a
// different slot of gc's table. The observable is how many times the
// handed-over key k itself is produced: 1 = the re-created entry was
// skipped, 2 = it was produced again. gc EXHIBITS BOTH members here
// (size 3, one fresh insert: n=2 in 17,451/20,000 trials at
// GOMAXPROCS=8; the fresh-insert sweep 0..8 is in the evidence dir
// docs/evidence/2026-09-02_e9-cross-goroutine-prune/), so before the
// foreign prune this row was a differential MISMATCH (observed ∉
// modeled), not only a permitted-∉-modeled envelope gap. The fresh key
// is a created entry — it may be produced or skipped — but it does not
// enter the observable.
func crossGoroutineDeleteReAddInsert() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	req := make(chan int)
	ack := make(chan int)
	go func() {
		k := <-req
		delete(m, k)
		m[101] = 101
		m[k] = k + 10
		ack <- 0
	}()
	kcount := 0
	first := true
	k0 := 0
	for k := range m {
		if first {
			first = false
			k0 = k
			kcount++
			req <- k
			<-ack
			continue
		}
		if k == k0 {
			kcount++
		}
	}
	return kcount
}

// The UNSYNCHRONIZED control: B deletes and re-inserts key 1 with no
// handshake (only the spawn edge and the final join order it), so B's
// delete (a write to the map cell) and A's pick-time loads are
// HB-unordered on EVERY schedule — the racy lane: every enumerated path
// refuses, `go run -race` red (exit 66 at the probe). The join keeps B's
// accesses inside every path (main cannot exit before B ran).
func crossGoroutineDeleteReAddRacy() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	done := make(chan int)
	go func() {
		delete(m, 1)
		m[1] = 11
		done <- 0
	}()
	sum := 0
	for k := range m {
		sum += k
	}
	<-done
	return sum
}

func main() {
	println(crossGoroutineDeleteReAdd())
	println(crossGoroutineDeleteReAddInsert())
	println(crossGoroutineDeleteReAddRacy())
}
