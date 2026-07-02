package main

type overlapInt int

type badOverlap interface {
	~int | overlapInt
}
