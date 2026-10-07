package main

const k = "hello"

func lit() int  { b := []byte("hello"); return cap(b) }
func cst() int  { b := []byte(k); return cap(b) }
func cat() int  { b := []byte("hel" + "lo"); return cap(b) }
func vr() int   { s := "hello"; b := []byte(s); return cap(b) }
func rl() int   { r := []rune("héllo"); return cap(r) }
func rv() int   { s := "héllo"; r := []rune(s); return cap(r) }
func nest() int { return len([]byte("hello")) + cap([]byte(k)) }

func main() { println(lit(), cst(), cat(), vr(), rl(), rv(), nest()) }
