// spec#String_literals block String_literals-2-d7b1cc56: "\U00110000" illegal: invalid Unicode code point
package main

const _ = "\U00110000"

func main() {}
