// R1 probe (acceptance entanglement): this program COMPILES only where
// int is 64-bit — the constant 1<<62 overflows a 32-bit int at compile
// time. The negative lane inherits the width pin through acceptance.
package main

const big int = 1 << 62

func main() {
	println(big)
}
