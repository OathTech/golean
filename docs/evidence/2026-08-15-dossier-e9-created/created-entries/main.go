// E9-created probe: entries CREATED during map iteration "may be
// produced during the iteration or may be skipped" (spec §For
// statements). 200 independent iterations, each inserting 8 fresh
// keys (>= 100) while ranging over a 4-entry map; count how many runs
// produce at least one created entry, and how many created entries
// are produced in total.
package main

func main() {
	runsWithProduced := 0
	totalProduced := 0
	const runs = 200
	for r := 0; r < runs; r++ {
		m := map[int]int{0: 0, 1: 1, 2: 2, 3: 3}
		inserted := 0
		producedThisRun := 0
		for k := range m {
			if k >= 100 {
				producedThisRun++
			}
			if inserted < 8 {
				m[100+8*r+inserted] = 1
				inserted++
			}
		}
		totalProduced += producedThisRun
		if producedThisRun > 0 {
			runsWithProduced++
		}
	}
	println("runs:", runs, "| runs producing >=1 created entry:", runsWithProduced, "| total created entries produced:", totalProduced)
}
