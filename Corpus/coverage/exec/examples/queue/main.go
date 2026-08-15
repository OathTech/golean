package main

import "fmt"

// Queue via slice: enqueue appends at the back, dequeue takes from the
// front (re-slice q[1:]). FIFO order is the property of interest —
// contrast with the sibling stack example, which is LIFO.

func enqueue(q []uint64, v uint64) []uint64 {
	return append(q, v)
}

func dequeue(q []uint64) ([]uint64, uint64) {
	v := q[0]
	return q[1:], v
}

func front(q []uint64) uint64 {
	return q[0]
}

func qsize(q []uint64) uint64 {
	return uint64(len(q))
}

// enqDeqThree: enqueue a, b, c, then dequeue all three; the returned
// triple is in dequeue order, so FIFO means it comes back (a, b, c).
func enqDeqThree(a, b, c uint64) (uint64, uint64, uint64) {
	q := []uint64{}
	q = enqueue(q, a)
	q = enqueue(q, b)
	q = enqueue(q, c)
	var x, y, z uint64
	q, x = dequeue(q)
	q, y = dequeue(q)
	q, z = dequeue(q)
	return x, y, z
}

// enqFront: after enqueue a then b, the front is still a (FIFO).
func enqFront(a, b uint64) uint64 {
	q := []uint64{}
	q = enqueue(q, a)
	q = enqueue(q, b)
	return front(q)
}

func emptyQSize() uint64 {
	q := []uint64{}
	return qsize(q)
}

// queueCapN: the fixed observation cap of the S3 relational harness.
const queueCapN = 8

// queue_harness_r: the S3 RELATIONAL harness. Setup enqueues the
// family seed + i (wrapping) for i < n, recording each value into
// `enqueued`; then it dequeues min(k, n) values — the min written
// explicitly below — recording them in dequeue order into `dequeued`;
// the third observable is the remaining size. FIFO means
// dequeued[i] = enqueued[i] for i < min(k, n). Real Go, rung 0.
func queue_harness_r(n, seed, k uint64) ([queueCapN]uint64, [queueCapN]uint64, uint64) {
	q := []uint64{}
	var enqueued [queueCapN]uint64
	for i := uint64(0); i < n; i++ {
		v := seed + i
		q = enqueue(q, v)
		enqueued[i] = v
	}
	d := k
	if n < k {
		d = n
	}
	var dequeued [queueCapN]uint64
	for i := uint64(0); i < d; i++ {
		var v uint64
		q, v = dequeue(q)
		dequeued[i] = v
	}
	return enqueued, dequeued, qsize(q)
}

func main() {
	x, y, z := enqDeqThree(1, 2, 3)
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		x, y, z,
	)
}
