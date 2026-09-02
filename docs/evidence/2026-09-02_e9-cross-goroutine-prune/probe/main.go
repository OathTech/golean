// E9 cross-goroutine delete-then-re-create probe (GoLean Tier-5 slice,
// 2026-09-02). Goroutine A (main) ranges over m; on its FIRST production
// it hands the produced key k to goroutine B over a channel; B deletes k,
// re-inserts k, and acks; A continues the range. Observable: the number
// of productions n (size = the re-created key was SKIPPED; size+1 = it
// was PRODUCED AGAIN; -1 = more than that, truncated). Every map access
// is HB-ordered by the req/ack handshake (DRF, -race green).
//
// Mode "racy": B deletes/re-inserts WITHOUT the handshake (only the
// spawn edge and a final join order it) — the unsynchronized control,
// -race red.
package main

import (
	"fmt"
	"os"
	"runtime"
	"strconv"
)

func trialDRF(size int) int {
	m := make(map[int]int)
	for i := 1; i <= size; i++ {
		m[i] = i
	}
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
		if n > size+1 {
			return -1
		}
		if first {
			first = false
			req <- k
			<-ack
		}
	}
	return n
}

func trialRacy(size int) int {
	m := make(map[int]int)
	for i := 1; i <= size; i++ {
		m[i] = i
	}
	done := make(chan int)
	go func() {
		delete(m, 1)
		m[1] = 11
		done <- 0
	}()
	n := 0
	for range m {
		n++
		if n > size+1 {
			break
		}
	}
	<-done
	return n
}


// Mode "grow": as DRF, but B also inserts `size` FRESH keys (forcing a
// map growth/relocation) between the delete and the re-insert of k.
// Observable: how many times the handed-over key k itself is produced
// (1 = skipped after re-creation, 2 = produced again).
var freshN = 3

func trialGrow(size int) int {
	m := make(map[int]int)
	for i := 1; i <= size; i++ {
		m[i] = i
	}
	req := make(chan int)
	ack := make(chan int)
	go func() {
		k := <-req
		delete(m, k)
		for i := 1; i <= freshN; i++ {
			m[1000000+i] = i
		}
		m[k] = k + 10
		ack <- 0
	}()
	kcount := 0
	first := true
	var k0 int
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

func main() {
	mode := os.Args[1]
	trials, _ := strconv.Atoi(os.Args[2])
	size, _ := strconv.Atoi(os.Args[3])
	if len(os.Args) > 4 {
		freshN, _ = strconv.Atoi(os.Args[4])
	}
	counts := map[int]int{}
	for i := 0; i < trials; i++ {
		if mode == "racy" {
			counts[trialRacy(size)]++
		} else if mode == "grow" {
			counts[trialGrow(size)]++
		} else {
			counts[trialDRF(size)]++
		}
	}
	fmt.Printf("mode=%s GOMAXPROCS=%d size=%d fresh=%d trials=%d ->", mode, runtime.GOMAXPROCS(0), size, freshN, trials)
	keys := []int{-1, size, size + 1}
	if mode == "grow" {
		keys = []int{1, 2}
	}
	for _, k := range keys {
		fmt.Printf(" n=%d:%d", k, counts[k])
	}
	other := 0
	for k, c := range counts {
		hit := false
		for _, kk := range keys {
			if k == kk {
				hit = true
			}
		}
		if !hit {
			other += c
		}
	}
	fmt.Printf(" other:%d\n", other)
}
