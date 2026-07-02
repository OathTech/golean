package main

type badEmbeddedPointerType *int

type badEmbeddedPointer struct {
	badEmbeddedPointerType
}
