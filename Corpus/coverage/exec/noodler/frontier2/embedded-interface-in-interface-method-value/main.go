// noodler frontier probe — method value via struct-embedded interface embedding an interface
package main

type Reader interface{ Read() int }
type ReadCloser interface {
	Reader
	Close() int
}
type file struct{ n int }

func (f file) Read() int  { return f.n }
func (f file) Close() int { return -f.n }

type wrapper struct{ ReadCloser }

// Method value through struct-embedded interface that itself embeds an
// interface; assignment of the wrapper to the narrower interface.
func embeddedInterfaceInInterfaceMethodValue() int {
	w := wrapper{file{4}}
	rd := w.Read
	var r Reader = w
	return rd()*10 + r.Read() + w.Close()
}

func main() {}
