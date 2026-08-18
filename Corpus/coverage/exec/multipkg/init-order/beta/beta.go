package beta

import "reclog"

// B records WHEN beta initialized (the push count), pinning that beta
// runs after both of alpha's events despite main importing beta first.
var B int

func init() {
	B = reclog.Push(3)
}
