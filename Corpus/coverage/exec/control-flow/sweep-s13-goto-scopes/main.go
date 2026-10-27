package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: binding under the
// goto envelope (emitGotoBody: top-level declarations hoisted to the body's
// head, deeper blocks re-executed wholesale) — a goto past an inner block
// holding a declaration (legal: no variable comes into scope), a goto over a
// const declaration, a backward goto re-running `var x int` (re-zeroed), a
// named-result shadow in a nested block of a goto body, and the per-iteration
// for-clause loop left by a goto or re-run by a backward goto.
// control-flow/goto-backward-redeclare holds the re-run `:=`; the captured and
// address-taken hoisted shapes refuse by name (FR-11). Expected = gc go1.26.5.

// I2
func gotoPastInnerBlockDecl() int {
	i := 0
	goto skip
	{
		x := 1
		i += x
	}
skip:
	return i + 5 // 5
}

// I3
func gotoOverConst() int {
	goto done
	const c = 1
done:
	return 7
}

// I4b
func gotoBackwardVarRezero() int {
	n := 0
	sum := 0
loop:
	var x int
	x += n
	sum += x
	n++
	if n < 3 {
		goto loop
	}
	return sum // 3
}

// A24a
func resultShadowInGotoBody() (r int) {
	r = 1
	n := 0
again:
	{
		r := 10
		r += n
		_ = r
	}
	n++
	if n < 2 {
		goto again
	}
	return // 1
}

// D7
func gotoOutOfPeriterLoop() int {
	var fs []func() int
	for i := 0; i < 10; i++ {
		fs = append(fs, func() int { return i })
		if i == 2 {
			goto out
		}
	}
out:
	return fs[0]()*100 + fs[1]()*10 + fs[2]() // 12
}

// D7b
func gotoRerunPeriterLoop() int {
	var fs []func() int
	round := 0
top:
	for i := 0; i < 2; i++ {
		fs = append(fs, func() int { return i })
	}
	round++
	if round < 2 {
		goto top
	}
	return fs[0]()*1000 + fs[1]()*100 + fs[2]()*10 + fs[3]() // 101
}

func main() {
	println(gotoPastInnerBlockDecl(), gotoOverConst(), gotoBackwardVarRezero(), resultShadowInGotoBody(),
		gotoOutOfPeriterLoop(), gotoRerunPeriterLoop())
}
