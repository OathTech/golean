// Sweep lane sweep/s3-type-keys (2026-10-26), shape S3 «type identity keys: fusion or
// spurious distinction» of the defect-neighbourhood campaign
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4; the matrix and the probe ids are on the
// `- Neighbourhood:` lines of BUG-124/098/100/097/092/067/010/018 in docs/BUGS.md). Every row
// is strict, expected = gc go1.26.5; each subject is one cell (type kind × route) of the matrix,
// born green: the machine agreed with gc on every one at the lane base 89ba27c5.
package main

// K16 stdlib same-named types: html/template.Template ≢ text/template.Template (BUG-010's
// pair, R1 pinned) on the other routes; a second pair encoding/json.Decoder ≢
// encoding/xml.Decoder on R1.

import (
	"encoding/json"
	"encoding/xml"
	ht "html/template"
	tt "text/template"
)

// R3
func stdlibSwitch() int {
	var h *ht.Template
	var t *tt.Template
	r := 0
	for _, v := range []any{h, t} {
		d := 0
		switch v.(type) {
		case *tt.Template:
			d = 1
		case *ht.Template:
			d = 2
		}
		r = r*10 + d
	}
	return r // 21
}

// R4
func stdlibEqual() int {
	var h *ht.Template
	var t *tt.Template
	s := 0
	if any(h) == any(t) {
		s += 1
	}
	if any(h) == any((*ht.Template)(nil)) {
		s += 10
	}
	return s // 10
}

// R5
func stdlibMapKeys() int {
	var h *ht.Template
	var t *tt.Template
	m := map[any]int{}
	m[h] = 1
	m[t] = 2
	m[(*ht.Template)(nil)] = 3
	return len(m)*10 + m[h] // 23
}

// R1 second pair.
func stdlibDecoderAssert() int {
	var j *json.Decoder
	s := 0
	if _, ok := any(j).(*xml.Decoder); ok {
		s += 1
	}
	if _, ok := any(j).(*json.Decoder); ok {
		s += 10
	}
	return s // 10
}

// R2
func stdlibPanic() int {
	var h *ht.Template
	var x any = h
	_ = x.(*tt.Template)
	return 0
}

func main() {}
