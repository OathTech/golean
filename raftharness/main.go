package main

import (
	"context"
	crand "crypto/rand"
	"encoding/binary"
	"flag"
	"fmt"
	"os"
	"time"
)

func main() {
	var (
		scenario = flag.String("scenario", "all", "scenario name, or 'all'")
		seed     = flag.Uint64("seed", 0, "base seed (0 = random; printed for repro)")
		iters    = flag.Int("iters", 3, "iterations per scenario (seed+i each)")
	)
	flag.Parse()

	base := *seed
	if base == 0 {
		var b [8]byte
		if _, err := crand.Read(b[:]); err != nil {
			panic(err)
		}
		base = binary.LittleEndian.Uint64(b[:])
	}
	fmt.Printf("raftharness: base seed %#x, %d iteration(s) per scenario\n", base, *iters)

	failures := 0
	for _, s := range scenarios {
		if *scenario != "all" && *scenario != s.Name {
			continue
		}
		for i := 0; i < *iters; i++ {
			iterSeed := base + uint64(i)
			ctx, cancel := context.WithTimeout(context.Background(), s.Budget)
			start := time.Now()
			err := s.Run(ctx, iterSeed)
			cancel()
			if err != nil {
				failures++
				fmt.Printf("FAIL  %-14s seed=%#x  %6.2fs\n      %v\n", s.Name, iterSeed, time.Since(start).Seconds(), err)
			} else {
				fmt.Printf("pass  %-14s seed=%#x  %6.2fs\n", s.Name, iterSeed, time.Since(start).Seconds())
			}
		}
	}
	if failures > 0 {
		fmt.Printf("raftharness: %d FAILURE(S)\n", failures)
		os.Exit(1)
	}
	fmt.Println("raftharness: all green")
}
