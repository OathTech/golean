package main

import "sync"

// go_mem-RACY, TSan-GREEN shapes — the DESIGNED divergence from the
// `-race` oracle (Q-U4RESIDUAL, RULED [USER] 2026-09-02 option (A):
// "follow go_mem exactly"; docs/2026-08-31_qrow-rulings.md row 9;
// docs/BUGS.md BUG-084). Every subject performs a PLAIN access (a
// whole-struct copy = read, a whole-struct overwrite = write) to a
// primitive beside a sync op that gc's -race build runs under
// `race.Disable` — so TSan sees nothing and gc runs to a value — but
// that mem#model kinds WRITE-LIKE (RWMutex RUnlock/Unlock: "mutex
// unlock"; WaitGroup Add/Done: the counter RMW) or, for the overwrite,
// READ-LIKE (Wait: the counter read). By mem#model's read-write /
// write-write data-race definitions ("at least one of which is
// non-synchronizing") each is a data race; mem#restrictions licenses
// the implementation to "report the race and halt" — the machine does.
//
// THESE ROWS ARE RED BY DESIGN and never count as a pass: expected_status
// is gc's observation (`ok`, the value) and the machine refuses with
// `race` on every path, so each row FAILs at lean-observation. They sit
// on BUG-084's Cases line (a Pinned-by:none red-by-design pin, the
// BUG-070/078 precedent) so the divergence stays visible and can never
// be laundered into a pass by a baseline re-pin. Every shape is a vet
// `copylocks` violation; no race-free program is affected. Shapes whose
// gc outcome is schedule-dependent (an overwrite beside Done, whose
// reset counter makes the Done a negative-counter panic on some
// schedules) are probed, not pinned here: probes/u4kind
// `wg-overwrite-vs-done` (docs/evidence/2026-09-02_q-u4-gomem/). So is an
// overwrite beside an Add from a NONZERO counter (audit fix F1): when the
// racing overwrite lands first the counter is reset to 0, the Add IS the
// counter-off-0 case and gc executes `race.Read(&wg.sema)` (waitgroup.go:
// 111-115) — TSan-red on those schedules, green when the Add lands first;
// refused on every path here. Corpus-pinnable in no lane (a green -race
// sample fails a racy row, a red one an ok row): probes/u4gomem
// `wg-overwrite-vs-add-nonzero`.
//
// Every copy lands in a package-level sink so the compiler cannot narrow
// the struct read to one field.

type gomemRwBox struct {
	rw sync.RWMutex
	n  int
}

type gomemWgBox struct {
	wg sync.WaitGroup
	n  int
}

var (
	gomemRwSink gomemRwBox
	gomemWgSink gomemWgBox
)

// Copy beside RUnlock ONLY: main RLocks before the spawn (sequenced
// before the child), the child RUnlocks (legal, owner-free — rwmutex.go
// documents the arrangement), main copies. mem#model: unlock is
// write-like, the copy read-like and non-synchronizing → a read-write
// data race. TSan: RUnlock's only instrumented access is the plain
// `race.Read(&rw.w)`, read/read with the copy → green.
func gomemRwCopyVsRUnlock() int {
	var r gomemRwBox
	done := make(chan int)
	r.rw.RLock()
	go func() {
		r.rw.RUnlock()
		done <- 0
	}()
	gomemRwSink = r
	<-done
	return gomemRwSink.n
}

// Copy beside the write-Unlock ONLY (main Locks before the spawn; the
// child Unlocks). Same derivation as above.
func gomemRwCopyVsUnlock() int {
	var r gomemRwBox
	done := make(chan int)
	r.rw.Lock()
	go func() {
		r.rw.Unlock()
		done <- 0
	}()
	gomemRwSink = r
	<-done
	return gomemRwSink.n
}

// Copy beside Add(1) taking the counter off 0 (then Done). mem#model:
// the counter RMW is write-like. TSan: Add-from-0's realized access is
// the plain READ of wg.sema, read/read with the copy → green.
func gomemWgCopyVsAddFrom0() int {
	var w gomemWgBox
	done := make(chan int)
	go func() {
		w.wg.Add(1)
		w.wg.Done()
		done <- 0
	}()
	gomemWgSink = w
	<-done
	return gomemWgSink.n
}

// Copy beside Done ONLY (main Adds before the spawn). mem#model: Done
// is write-like (it "synchronizes before" the Wait it unblocks — the
// release shape). TSan: Done's state Add is under race.Disable → green.
func gomemWgCopyVsDone() int {
	var w gomemWgBox
	done := make(chan int)
	w.wg.Add(1)
	go func() {
		w.wg.Done()
		done <- 0
	}()
	gomemWgSink = w
	<-done
	return gomemWgSink.n
}

// Overwrite beside a Wait that returns at counter 0. mem#model: the
// counter read is read-like, the overwrite a plain write → read-write
// race. TSan: a Wait at 0 registers no waiter and touches nothing it
// instruments → green.
func gomemWgOverwriteVsWaitAt0() int {
	var w gomemWgBox
	done := make(chan int)
	go func() {
		w.wg.Wait()
		done <- 0
	}()
	w = gomemWgBox{}
	<-done
	return w.n
}

func main() {
	println(gomemRwCopyVsRUnlock(), gomemRwCopyVsUnlock(), gomemWgCopyVsAddFrom0(),
		gomemWgCopyVsDone(), gomemWgOverwriteVsWaitAt0())
}
