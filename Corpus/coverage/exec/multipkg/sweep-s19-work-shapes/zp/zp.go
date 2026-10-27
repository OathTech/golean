package zp

// A field read of a global struct: ODOT of a non-literal — work.
type zst struct{ f int }

var zs = zst{4}
var P = zs.f
