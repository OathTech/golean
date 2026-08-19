package bbb

import "rec"

// bbb imports ONLY rec, so it is ready as soon as rec is initialized.
// B records WHEN bbb initialized (the push count).
var B int

func init() {
	B = rec.Push(2)
}
