// spec#General_interfaces block General_interfaces-2-46b76d35: ~MyInt illegal: in ~T the underlying type of T must be itself
package main

type MyInt int

type C interface {
	~MyInt // illegal: the underlying type of MyInt is not MyInt
}

func main() {}
