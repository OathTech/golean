package zc

// uint -> uintptr: SimType[TUINTPTR] == TUINT64 — OCONVNOP, folded.
var zv uint = 3
var C = uintptr(zv)
