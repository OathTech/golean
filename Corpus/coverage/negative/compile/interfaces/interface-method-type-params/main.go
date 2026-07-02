package main

type badGenericInterfaceMethod interface {
	m[T any](T)
}
