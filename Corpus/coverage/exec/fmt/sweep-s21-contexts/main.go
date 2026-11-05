package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Groups C8 / I6: the fmt desugars from package-level initializers and init() (the forms whose helpers reference no refusal
// arm: %d / %x / Errorf), a method, a goroutine, a deferred call, a generic body.
import (
	"fmt"
	"sync"
)

var g = fmt.Sprintf("%d-%x", 1, uint8(255))
var ge = fmt.Errorf("e%d", 2)
var gi string

func init() { gi = fmt.Sprintf("%d", 3) + fmt.Errorf("i%x", uint8(4)).Error() }

type rec struct{ n int }

func (r rec) text() string { return fmt.Sprintf("r%d", r.n) }

func show[T any](x T) string { return fmt.Sprint(x) }

func initializers() (string, string, string) { return g, ge.Error(), gi }
func inMethod() string                       { return rec{4}.text() }
func inGoroutine() string {
	ch := make(chan string, 1)
	var wg sync.WaitGroup
	wg.Add(1)
	go func() { defer wg.Done(); ch <- fmt.Sprintf("g%d", 5) + fmt.Sprint("|", 6) }()
	wg.Wait()
	return <-ch
}
func inDefer() (out string) {
	defer func() { out = fmt.Sprintf("%s!", out) + fmt.Sprintln(out) }()
	return "d"
}
func genericSprint() string { return show(5) + "|" + show("s") + "|" + show(true) }

type tagged struct{}

func (tagged) goleanShimFmtUint(v uint64) string { return "method" }

func shimNamedMethod() string { return tagged{}.goleanShimFmtUint(1) + fmt.Sprintf("%d", uint8(2)) }
func deadSiteOnly() string    { return "live" }
func dead() string            { return fmt.Sprintf("%q", "never called") }

func main() {
	initializers()
	inMethod()
	inGoroutine()
	inDefer()
	genericSprint()
	shimNamedMethod()
	deadSiteOnly()
}
