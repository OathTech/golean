package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: a strict row (expected = gc go1.26.5 under the
// runners' pins) on a route no earlier row held; the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4.
// A8, go/build goodOSArchFile on linux/amd64: x_arm64_linux.go (the OS token last
// wins: included, +1), x_unix.go (unix is not a filename tag: included, +10),
// linux_amd64.go (no prefix before the first _, the arch token: included, +100),
// linux_arm64.go (arch token arm64: excluded, +1000 never added), x_android.go
// (android is not linux: excluded, +10000 never added), x_amd64_linux.go (OS token
// last: included, +100000). gc: 100111.

var x = 0

func suffixTokens() int { return x }
