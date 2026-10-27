package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: a strict row (expected = gc go1.26.5 under the
// runners' pins) on a route no earlier row held; the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4.
// A27: the file has CRLF line endings; the raw string spans a line break and the
// carriage return is discarded from its value (spec#String_literals): len 5, and
// s[2] is the newline: 5*10 + int(byte('\n') - 'a') = 50 + 169.

const s = `ab
cd`

func crlfRawString() int { return len(s)*10 + int(s[2]-'a') }
