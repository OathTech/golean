// spec#General_interfaces block General_interfaces-4-51fa039a: ~P term illegal: the type in a term T or ~T cannot be a type parameter
package main

func f[P any, _ interface{ int | ~P }]() {} // illegal: P is a type parameter

func main() {}
