package main

import "sync/atomic"
type Alias = uintptr
type Named uintptr
func takesPointer(x uintptr) uintptr { return x }
func aliasIdentity() bool { var a any = Alias(7); _, ok := a.(uintptr); return ok }
func namedIdentity() bool { var a any = Named(7); _, bad := a.(uintptr); _, good := a.(Named); return good && !bad }
func functionIdentity() bool { var a any = takesPointer; _, bad := a.(func(uint64) uint64); _, good := a.(func(uintptr) uintptr); return good && !bad }
func channelIdentity() bool { var a any = make(chan uintptr); _, bad := a.(chan uint64); _, good := a.(chan uintptr); return good && !bad }
func mapIdentity() bool { var a any = map[uintptr]uintptr{7: 8}; _, bad := a.(map[uint64]uint64); _, good := a.(map[uintptr]uintptr); return good && !bad }
func conversion() bool { x := int64(-1); y := uintptr(x); return y == ^uintptr(0) && int64(y) == -1 && uint64(y) == ^uint64(0) }
func atomicIdentity() bool { var x uintptr; atomic.StoreUintptr(&x, ^uintptr(0)); var a any = atomic.AddUintptr(&x, 1); _, bad := a.(uint64); v, good := a.(uintptr); return good && !bad && v == 0 }
func highReadout() uintptr { return ^uintptr(0) }
func main() { println(aliasIdentity(), namedIdentity(), functionIdentity(), channelIdentity(), mapIdentity(), conversion(), atomicIdentity(), highReadout()) }
