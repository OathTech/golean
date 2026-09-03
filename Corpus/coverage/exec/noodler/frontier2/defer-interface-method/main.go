// noodler frontier probe — defer i.M() through an interface, receiver snapshot at defer time
package main

type Closer interface{ Close() }
type rec struct{ log *int }

func (r rec) Close() { *r.log = *r.log*10 + 1 }

// defer of an interface method call: receiver (the interface value) is
// evaluated at defer time.
func deferInterfaceMethod() int {
	log := 0
	var c Closer = rec{&log}
	func() {
		defer c.Close()
		c = nil
		log = 5
	}()
	return log
}

func main() {}
