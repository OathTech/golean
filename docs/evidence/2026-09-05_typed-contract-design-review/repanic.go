package main

func main() {
 defer func() {
  _ = recover()
  panic("same")
 }()
 panic("same")
}
