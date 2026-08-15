package main

import (
	"fmt"
	"strings"
)

// wordFreq: the subject — split the text into words with
// strings.Fields (the idiomatic Go spelling this example exists to
// exercise: extension E5, the stdlib-shim boundary), count each word
// in a map, and report the queried word's count plus the maximum
// count over all words. The max loop RANGES over the map, so its
// iteration order is nondeterministic; the summary is order-invariant
// by construction. `counts[query]` on an absent key is Go's
// zero-value read.
func wordFreq(text string, query string) (uint64, uint64) {
	words := strings.Fields(text)
	counts := make(map[string]uint64)
	for i := 0; i < len(words); i++ {
		counts[words[i]]++
	}
	best := uint64(0)
	for _, c := range counts {
		if c > best {
			best = c
		}
	}
	return counts[query], best
}

func wfBasic() (uint64, uint64) {
	return wordFreq("the quick fox the lazy dog the", "the")
}

func wfAllSame() (uint64, uint64) {
	return wordFreq("go go go", "go")
}

func wfMiss() (uint64, uint64) {
	return wordFreq("alpha beta  gamma", "delta")
}

func wfEmpty() (uint64, uint64) {
	return wordFreq("", "alpha")
}

func wfSpaceOnly() (uint64, uint64) {
	return wordFreq(" \t\n\v\f\r ", "alpha")
}

func wfTabsNewlines() (uint64, uint64) {
	return wordFreq("\tgo  fn\ngo\t\tfn go\n", "fn")
}

// buildText: the differential driver passes only integer arguments,
// so the harness builds its text from (n, seed): n single-letter
// words from the family {"a","b","c"} (word i = 'a' + (seed+i)%3,
// Go's own uint64 wrap in seed+i kept honestly), with the separator
// VARIED by position — one space, two spaces, or a tab — and a
// leading space, so Fields' leading/trailing/consecutive/mixed
// whitespace classes are exercised on every built input.
func buildText(n, seed uint64) string {
	out := " "
	for i := uint64(0); i < n; i++ {
		out += string(rune(97 + (seed+i)%3))
		if i%3 == 0 {
			out += " "
		} else if i%3 == 1 {
			out += "  "
		} else {
			out += "\t"
		}
	}
	return out
}

// wordfreq_harness_r: the S3 RELATIONAL harness — setup builds the
// text and the queried word from (n, seed, qsel); the returned
// quadruple (pre, q, hits, best) is the observable, all pure values
// (strings cross the observation boundary by contents). The
// postcondition relates the RETURNED data: hits = the multiplicity
// of q among pre's words, best = the maximum multiplicity.
func wordfreq_harness_r(n, seed, qsel uint64) (string, string, uint64, uint64) {
	pre := buildText(n, seed)
	q := string(rune(97 + qsel%3))
	hits, best := wordFreq(pre, q)
	return pre, q, hits, best
}

func main() {
	hits, best := wfBasic()
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		hits, best,
	)
}
