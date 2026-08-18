// spec#Rune_literals block Rune_literals-3-57f8f4f9: '\U00110000' illegal: invalid Unicode code point (above 0x10FFFF)
package main

const _ = '\U00110000'

func main() {}
