package main

// spec#Embedded_interfaces block Embedded_interfaces-1-bf873c1a: ReadWriter
// embeds Reader and Writer; its method set is the UNION Read, Write, Close —
// methods with the same name and identical signature (Close) may appear
// through multiple embedded interfaces. A ReadWriter value therefore
// satisfies Reader and Writer too.

type Reader interface {
	Read(p []byte) (n int, err error)
	Close() error
}

type Writer interface {
	Write(p []byte) (n int, err error)
	Close() error
}

// ReadWriter's methods are Read, Write, and Close.
type ReadWriter interface {
	Reader // includes methods of Reader in ReadWriter's method set
	Writer // includes methods of Writer in ReadWriter's method set
}

type rwImpl struct{ log string }

func (x *rwImpl) Read(p []byte) (n int, err error)  { x.log += "R"; return len(p), nil }
func (x *rwImpl) Write(p []byte) (n int, err error) { x.log += "W"; return len(p), nil }
func (x *rwImpl) Close() error                      { x.log += "C"; return nil }

func embeddedReadWriter() string {
	x := &rwImpl{}
	var rw ReadWriter = x
	n1, e1 := rw.Read(make([]byte, 2))
	n2, e2 := rw.Write(make([]byte, 3))
	e3 := rw.Close()
	var r Reader = rw // ReadWriter satisfies Reader
	var w Writer = rw // ... and Writer
	_, _ = r.Read(nil)
	_, _ = w.Write(nil)
	ok := "nil"
	if e1 != nil || e2 != nil || e3 != nil {
		ok = "err"
	}
	return x.log + "|" + string(rune('0'+n1)) + string(rune('0'+n2)) + "|" + ok // "RWCRW|23|nil"
}
