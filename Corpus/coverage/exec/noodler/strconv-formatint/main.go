// noodler probe — strconv.FormatInt used WITHOUT strconv.FormatUint in
// the same program (the shim allowlist's FormatInt entry; D-002 keeps
// the surface frozen, this row pins the allowlisted function alone).
package main

import "strconv"

// strconv.FormatInt with negative values and bases.
func formatIntEdges() (string, string, string) {
	return strconv.FormatInt(-255, 16), strconv.FormatInt(-1<<63, 2), strconv.FormatInt(35, 36)
}

// A plain positive FormatInt in base 10.
func formatIntPositive() string {
	x := int64(42)
	return strconv.FormatInt(x, 10)
}

func main() {}
