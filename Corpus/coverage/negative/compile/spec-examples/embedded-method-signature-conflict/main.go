// spec#Embedded_interfaces block Embedded_interfaces-2-0b6490ef: when embedding interfaces, methods with the same names must have identical signatures
package main

type Reader interface {
	Read(p []byte) (n int, err error)
	Close() error
}

type ReadCloser interface {
	Reader  // includes methods of Reader in ReadCloser's method set
	Close() // illegal: signatures of Reader.Close and Close are different
}

func main() {}
