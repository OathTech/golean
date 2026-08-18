// spec#String_literals block String_literals-2-d7b1cc56: "\uD800" illegal: surrogate half
package main

const _ = "\uD800"

func main() {}
