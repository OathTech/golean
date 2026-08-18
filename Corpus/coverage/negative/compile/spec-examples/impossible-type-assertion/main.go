// spec#Type_assertions block Type_assertions-2-f31bbf04: y.(string) illegal: string does not implement I (missing method m), assertion cannot hold
package main

import "io"

type I interface{ m() }

func f(y I) {
	s := y.(string)    // illegal: string does not implement I (missing method m)
	r := y.(io.Reader) // r has type io.Reader; dynamic type of y must implement both I and io.Reader
	_, _ = s, r
}

func main() {}
