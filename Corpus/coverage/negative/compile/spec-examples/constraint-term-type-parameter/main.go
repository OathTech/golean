// spec#General_interfaces block General_interfaces-4-51fa039a: type term cannot be a type parameter P
package main

func f[P any, _ interface{ P }]() {} // illegal: P is a type parameter

func main() {}
