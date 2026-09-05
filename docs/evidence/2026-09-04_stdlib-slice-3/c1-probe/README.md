# C1 probe — concurrent print at STATEMENT granularity (stdlib-slice-3 audit fix round, 2026-09-05)

[AGENT]. Consuming records: latitude inventory R18 (the obligation), ledger
FR-30, design note `docs/2026-09-04_stdlib-slice-3-design.md` §3.1/§4.

`main.go`: g1 = {print "a"; print "b"}, g2 = {print "c"}, joined on a
buffered channel; the combined fd-2 line is the observed order. The
machine's L1 scheduler consults only at registry boundaries and back-edges,
so g1's two prints are one atomic segment there and the enumerator admits
exactly {abc, cab}; gc's scheduler may preempt between the two statements
and realize `acb` (the audit reported 1/300).

Reproduction (repo root; go1.26.5 = the pin, deps/go c19862e5f8, linux/amd64,
shared 32-core box under other lanes' load):

    cd docs/evidence/2026-09-04_stdlib-slice-3/c1-probe
    GO111MODULE=off GOFLAGS= go build -o /tmp/c1probe . && GO111MODULE=off GOFLAGS= go build -race -o /tmp/c1probe-race .
    for i in $(seq 300); do /tmp/c1probe 2>&1; done | sort | uniq -c        # draws-plain.txt
    for i in $(seq 300); do /tmp/c1probe-race 2>&1; done | sort | uniq -c   # draws-race.txt

Result (this run, 2026-09-05): plain 298 cab / 2 abc; -race 149 cab / 151
abc; `acb` NOT exhibited in 600 draws. A sample that does not exhibit a
member is not a bound: the structural argument (gc preempts at any safe
point; the machine only at registry boundaries) stands, and the audit's
independent 1/300 observation is recorded as reported. Conclusion: no
corpus row over this shape (it would be observed∉modeled the moment gc
samples `acb`); FR-30 carries the fix direction.
