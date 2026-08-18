package zq

// The whole case in one line. `[3]int{1, 2, 3}` is not a CONSTANT — Go
// has no array constants, so go/types records no constant value for it
// — but it is entirely STATIC, and cmd/compile/internal/staticinit
// writes it straight into the data section. gc therefore emits no
// `..inittask` for zq; the frontend's syntactic rule keeps it.
//
// `zq` sorts after `la` and `lb`, so when it IS treated as a node it
// delays `la` past `lb` and the divergence is observable.
var A = [3]int{1, 2, 3}
