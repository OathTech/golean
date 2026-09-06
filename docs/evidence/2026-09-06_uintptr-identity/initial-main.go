package main

type U struct{}
func (U) M(x uintptr) {}
type Wants64 interface { M(uint64) }
func identity() int {
  out := 0
  var a any = uintptr(7)
  if _, ok := a.(uint64); ok { out += 1 }
  var b any = uint64(7)
  if _, ok := b.(uintptr); ok { out += 2 }
  var u any = U{}
  if _, ok := u.(Wants64); ok { out += 4 }
  if _, ok := a.(uintptr); ok { out += 8 }
  return out
}
func main() { println(identity()) }
