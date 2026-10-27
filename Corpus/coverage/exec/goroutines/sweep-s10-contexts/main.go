package main

// Sweep lane sweep/s10-panics (2026-10-27), shape S10: the run-time panic
// inside a SPAWNED goroutine — recovered there (the program continues: the
// child reports through a channel) or unrecovered (the whole program aborts
// with the child's panic, as goroutines/spawn-edge/ptr-box-child-aborts pins
// for the nil dereference) — at the nil-dereference, bounds and send-on-closed
// kinds.

func childRecoversNilDeref() int {
	done := make(chan int)
	go func() {
		r := 0
		func() {
			defer func() {
				if recover() != nil {
					r = 100
				}
			}()
			var p *int
			*p = 1
		}()
		done <- r
	}()
	return <-done
}

func childBoundsAborts() int {
	done := make(chan int)
	go func() {
		s := []int{1}
		i := len(s) + 4
		done <- s[i]
	}()
	return <-done
}

func childRecoversSendClosed() int {
	done := make(chan int)
	c := make(chan int)
	close(c)
	go func() {
		r := 0
		func() {
			defer func() {
				if recover() != nil {
					r = 100
				}
			}()
			c <- 1
		}()
		done <- r
	}()
	return <-done
}

func main() {}
