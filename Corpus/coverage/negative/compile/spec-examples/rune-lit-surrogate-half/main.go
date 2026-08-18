// spec#Rune_literals block Rune_literals-3-57f8f4f9: '\uDFFF' illegal: surrogate half
package main

const _ = '\uDFFF'

func main() {}
