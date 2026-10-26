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

	// The selection is VALIDATED before anything runs (deep-clean review
	// 2026-10-26, DC08 / validation V2; [USER] ruling of 2026-10-26, relayed):
	// an unknown -scenario matched nothing, a nonpositive -iters entered no
	// iteration, and the driver — judging only its failure counter — printed
	// «all green» having run nothing. A campaign that runs nothing is a
	// refusal (exit 2), never a pass.
	if flag.NArg() != 0 {
		fmt.Fprintf(os.Stderr, "raftharness: unexpected positional argument(s) %q — the harness takes flags only (-scenario, -seed, -iters)\n", flag.Args())
		os.Exit(2)
	}
	if *iters <= 0 {
		fmt.Fprintf(os.Stderr, "raftharness: -iters must be positive, got %d — a campaign of zero iterations runs nothing and proves nothing\n", *iters)
		os.Exit(2)
	}
	selected := 0
	names := make([]string, 0, len(scenarios))
	for _, s := range scenarios {
		names = append(names, s.Name)
		if *scenario == "all" || *scenario == s.Name {
			selected++
		}
	}
	if selected == 0 {
		fmt.Fprintf(os.Stderr, "raftharness: unknown scenario %q — the scenarios are %q, or 'all'\n", *scenario, names)
		os.Exit(2)
	}

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
	ran := 0
	for _, s := range scenarios {
		if *scenario != "all" && *scenario != s.Name {
			continue
		}
		for i := 0; i < *iters; i++ {
			ran++
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
		fmt.Printf("raftharness: %d FAILURE(S) in %d run(s)\n", failures, ran)
		os.Exit(1)
	}
	if ran != selected*(*iters) || ran == 0 {
		// Unreachable after the validation above; kept as the last line of
		// defence: a green verdict names the runs it rests on, or is none.
		fmt.Fprintf(os.Stderr, "raftharness: ran %d scenario iteration(s), expected %d — no verdict\n", ran, selected*(*iters))
		os.Exit(2)
	}
	fmt.Printf("raftharness: all green — %d run(s): %d scenario(s) x %d iteration(s)\n", ran, selected, *iters)
}
