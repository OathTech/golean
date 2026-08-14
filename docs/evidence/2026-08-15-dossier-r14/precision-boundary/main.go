// R14 probe: gc's realized integer-constant precision boundary.
// 1<<511 (a 512-bit value) is accepted; 1<<512 is rejected with
// "constant shift overflow" — gc's internal limit is 512 bits,
// twice the spec's 256-bit minimum, far below arbitrary precision.
package main

const c = 1 << 511

func main() { println(c / c) }
