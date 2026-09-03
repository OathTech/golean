# cedar-go census RELAX patch (pass B only; applied to the census COPY of
# types/datetime.go, never to deps/). The two package-level `time.Date`
# initializers are the library's whole-export kill point on main today:
# H-11 (tools/nativefrontend/emit.go quarantineUnlowerableGlobals) admits
# only os.Getenv/os.LookupEnv as pure unmodeled initializer callees, so
# ANY other package-selector call in a package-level initializer refuses
# the whole export. This rewrite turns the two constants into nullary
# functions and the single use site into calls — semantically identical
# under go run (time.Date is pure and deterministic), symmetric across
# both pipelines, and it moves the refusal from "whole export" to "two
# quarantined functions", which is what lets the per-declaration census
# be measured. [AGENT] 2026-09-03.
s|^var maxDatetime = time\.Date(|func maxDatetime() time.Time { return time.Date(|
s|^var minDatetime = time\.Date(|func minDatetime() time.Time { return time.Date(|
/^func maxDatetime() time.Time { return time.Date(/ s|)$|) }|
/^func minDatetime() time.Time { return time.Date(/ s|)$|) }|
s|t\.Before(minDatetime) \|\| t\.After(maxDatetime)|t.Before(minDatetime()) \|\| t.After(maxDatetime())|
