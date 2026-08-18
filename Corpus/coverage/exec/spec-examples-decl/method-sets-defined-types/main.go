package main

// spec#Type_definitions block Type_definitions-3-1cc92870: a defined type
// does NOT inherit methods (NewMutex has an empty method set but Mutex's
// composition — its field is still accessible); a struct EMBEDDING Mutex
// (PrintableMutex) gets Lock/Unlock promoted into *PrintableMutex's method
// set; MyBlock, defined from an interface, KEEPS the interface's method set.
// The spec's comment-only bodies are realized as a counter; Block is the
// section's earlier interface, declared here as support.

type Block interface {
	BlockSize() int
	Encrypt(src, dst []byte)
	Decrypt(src, dst []byte)
}

// A Mutex is a data type with two methods, Lock and Unlock.
type Mutex struct{ state int }

func (m *Mutex) Lock()   { m.state++ }
func (m *Mutex) Unlock() { m.state-- }

// NewMutex has the same composition as Mutex but its method set is empty.
type NewMutex Mutex

// The method set of PtrMutex's underlying type *Mutex remains unchanged,
// but the method set of PtrMutex is empty.
type PtrMutex *Mutex

// The method set of *PrintableMutex contains the methods
// Lock and Unlock bound to its embedded field Mutex.
type PrintableMutex struct {
	Mutex
}

// MyBlock is an interface type that has the same method set as Block.
type MyBlock Block

type cipher struct{}

func (cipher) BlockSize() int          { return 16 }
func (cipher) Encrypt(src, dst []byte) {}
func (cipher) Decrypt(src, dst []byte) {}

func promotedThroughEmbedding() int {
	var pm PrintableMutex
	pm.Lock() // promoted from the embedded Mutex
	pm.Lock()
	pm.Unlock()
	nm := NewMutex{state: 5} // same composition: the field exists
	var p PtrMutex = &pm.Mutex
	return pm.Mutex.state*100 + nm.state*10 + (*Mutex)(p).state // 100 + 50 + 1 = 151
}

func interfaceKeepsMethodSet() int {
	var mb MyBlock = cipher{}             // cipher implements Block, hence MyBlock
	var b Block = mb                      // identical method sets: assignable
	return mb.BlockSize() + b.BlockSize() // 32
}
