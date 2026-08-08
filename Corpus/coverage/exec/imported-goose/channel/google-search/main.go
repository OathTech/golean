// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/channel/google_search.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func Web(query string) string {
	return query + ".html"
}

func Image(query string) string {
	return query + ".png"
}

func Video(query string) string {
	return query + ".mp4"
}

// https://go.dev/talks/2012/concurrency.slide#46
func Google(query string) []string {
	c := make(chan string, 3)

	go func() { c <- Web(query) }()
	go func() { c <- Image(query) }()
	go func() { c <- Video(query) }()

	results := make([]string, 0, 3)
	for i := 0; i < 3; i++ {
		r := <-c
		results = append(results, r)
	}
	return results
}

// --- GoLean harness ---
// Authored wrapper: encodes the ARRIVAL ORDER of the three results as a
// three-digit code (Web=1, Image=2, Video=3) — the membership-lane
// observable.

func goleanGoogle() int {
	results := Google("q")
	code := 0
	for _, r := range results {
		d := 0
		if r == "q.html" {
			d = 1
		}
		if r == "q.png" {
			d = 2
		}
		if r == "q.mp4" {
			d = 3
		}
		code = code*10 + d
	}
	return code
}

func main() {}
