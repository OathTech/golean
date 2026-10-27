package main

// Sweep S19, lane sweep/s19-init-order, 2026-10-27 (cell B3): THREE files
// presented in file-name order (aa.go, bb.go, main.go — the go command's
// and the frontend's presentation). This file's variable depends on a
// variable declared in the LAST file: the dependency beats the file order
// (m from main.go initializes before a), while the `init` functions run
// strictly in file order after every variable (4, 5, 6).

var b3a = b3m*10 + mark(2)

func init() { mark(4) }
