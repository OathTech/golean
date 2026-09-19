commit fd99b0218bf34ea2cac78d96ada81f9559a3ec75  golean sha256 ab355547ff2377e2…  go version go1.26.5 linux/amd64  nproc 32  load1 start 0.97 end 0.99  started 2026-09-19T07:21:56Z

empty probe (startup): median 0.0201 s over 7 runs [0.0197..0.0216], rss 72636 KB

steps per loop iteration (fuel bisection): alloc_new=85, append_cap=84, append_grow=84, heap_then_scalar=70, heap_then_scalar=49, map_write=44, read_fixed=55, scalar=49, struct_arr_100=47, write_fixed=51

**(e) scalar loop — per-step baseline** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `scalar(10000,)` | 0.1704 | 0.1570..0.1718 | 0.16 | 0.1503 | 15.03 |
| `scalar(20000,)` | 0.2755 | 0.2724..0.3113 | 0.26 | 0.2554 | 12.77 |
| `scalar(40000,)` | 0.5428 | 0.5325..0.5724 | 0.53 | 0.5227 | 13.07 |
| `scalar(80000,)` | 1.0560 | 1.0482..1.2055 | 1.05 | 1.0359 | 12.95 |

successive net ratios — 10000→20000: ×1.70 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 20000→40000: ×2.05 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 40000→80000: ×1.98 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

per machine step at n=80000: 264 ns (49 steps/iteration)

**(a) the review's loop: `append` growing from nil** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `append_grow(250,)` | 0.0260 | 0.0259..0.0275 | 0.02 | 0.0059 | 23.60 |
| `append_grow(500,)` | 0.0336 | 0.0335..0.0342 | 0.02 | 0.0135 | 27.00 |
| `append_grow(1000,)` | 0.0477 | 0.0466..0.0504 | 0.04 | 0.0276 | 27.60 |
| `append_grow(2000,)` | 0.0800 | 0.0792..0.0814 | 0.07 | 0.0599 | 29.95 |
| `append_grow(4000,)` | 0.1383 | 0.1336..0.1479 | 0.13 | 0.1182 | 29.55 |

successive net ratios — 250→500: ×2.29 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 500→1000: ×2.04 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1000→2000: ×2.17 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 2000→4000: ×1.97 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(f) in-place `append`, w = c (no spill)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `append_cap(250, 250)` | 0.0266 | 0.0260..0.0269 | 0.02 | 0.0065 | 26.00 |
| `append_cap(500, 500)` | 0.0333 | 0.0331..0.0340 | 0.02 | 0.0132 | 26.40 |
| `append_cap(1000, 1000)` | 0.0474 | 0.0473..0.0489 | 0.04 | 0.0273 | 27.30 |
| `append_cap(2000, 2000)` | 0.0814 | 0.0760..0.0820 | 0.07 | 0.0613 | 30.65 |

successive net ratios — 250→500: ×2.03 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 500→1000: ×2.07 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1000→2000: ×2.25 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(f′) 100 in-place appends, capacity c varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `append_cap(100, 100)` | 0.0229 | 0.0227..0.0230 | 0.01 | 0.0028 | 28.00 |
| `append_cap(200, 100)` | 0.0224 | 0.0221..0.0225 | 0.01 | 0.0023 | 23.00 |
| `append_cap(400, 100)` | 0.0219 | 0.0218..0.0219 | 0.01 | 0.0018 | 18.00 |
| `append_cap(800, 100)` | 0.0218 | 0.0214..0.0218 | 0.01 | 0.0017 | 17.00 |
| `append_cap(1600, 100)` | 0.0222 | 0.0216..0.0222 | 0.01 | 0.0021 | 21.00 |
| `append_cap(3200, 100)` | 0.0228 | 0.0224..0.0237 | 0.01 | 0.0027 | 27.00 |
| `append_cap(6400, 100)` | 0.0239 | 0.0237..0.0240 | 0.01 | 0.0038 | 38.00 |

successive net ratios — 100→200: ×0.82 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 200→400: ×0.78 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1600→3200: ×1.29 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 3200→6400: ×1.41 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(b) 100 element writes `xs[0] = v`, slice length m varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `write_fixed(10, 100)` | 0.0207 | 0.0207..0.0210 | 0.01 | 0.0006 | 6.00 |
| `write_fixed(100, 100)` | 0.0209 | 0.0201..0.0215 | 0.01 | 0.0008 | 8.00 |
| `write_fixed(1000, 100)` | 0.0210 | 0.0208..0.0216 | 0.01 | 0.0009 | 9.00 |
| `write_fixed(3000, 100)` | 0.0215 | 0.0214..0.0217 | 0.01 | 0.0014 | 14.00 |
| `write_fixed(10000, 100)` | 0.0236 | 0.0230..0.0240 | 0.01 | 0.0035 | 35.00 |

**(b′) element writes at m = 10, write count varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `write_fixed(10, 100)` | 0.0207 | 0.0207..0.0210 | 0.01 | 0.0006 | 6.00 |
| `write_fixed(10, 1000)` | 0.0338 | 0.0338..0.0344 | 0.03 | 0.0137 | 13.70 |
| `write_fixed(10, 10000)` | 0.1651 | 0.1571..0.1734 | 0.16 | 0.1450 | 14.50 |

successive net ratios — 1000→10000: ×10.58 (linear ×10.0, quadratic ×100.0, cubic ×1000.0)

**(i) 1,000 element reads `xs[0]`, slice length m varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `read_fixed(10, 1000)` | 0.0364 | 0.0360..0.0365 | 0.03 | 0.0163 | 16.30 |
| `read_fixed(100, 1000)` | 0.0365 | 0.0364..0.0369 | 0.03 | 0.0164 | 16.40 |
| `read_fixed(1000, 1000)` | 0.0364 | 0.0358..0.0376 | 0.03 | 0.0163 | 16.30 |
| `read_fixed(10000, 1000)` | 0.0370 | 0.0369..0.0376 | 0.03 | 0.0169 | 16.90 |

successive net ratios — 10→100: ×1.01 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 100→1000: ×0.99 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 1000→10000: ×1.04 (linear ×10.0, quadratic ×100.0, cubic ×1000.0)

**(c) aggregate shape — 100 writes each** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| struct{y,x int}: s.x = i | 0.0206 | 0.0199..0.0206 | 0.01 | 0.0005 | 5.00 |
| struct{a [100]byte; x int}: s.x = i | 0.0204 | 0.0201..0.0206 | 0.01 | 0.0003 | 3.00 |
| struct{a [1000]byte; x int}: s.x = i | 0.0213 | 0.0212..0.0214 | 0.01 | 0.0012 | 12.00 |
| struct{a [10000]byte; x int}: s.x = i | 0.0223 | 0.0219..0.0224 | 0.01 | 0.0022 | 22.00 |
| struct{a []byte; x int}, len(a)=100: s.x = i | 0.0206 | 0.0205..0.0214 | 0.01 | 0.0005 | 5.00 |
| struct{a []byte; x int}, len(a)=10000: s.x = i | 0.0219 | 0.0214..0.0221 | 0.01 | 0.0018 | 18.00 |
| [10000]byte: b[0] = v | 0.0232 | 0.0230..0.0234 | 0.01 | 0.0031 | 31.00 |
| [10][1000]byte: a[0][0] = v | 0.0224 | 0.0219..0.0228 | 0.01 | 0.0023 | 23.00 |
| [100][100]byte: a[0][0] = v | 0.0218 | 0.0217..0.0220 | 0.01 | 0.0017 | 17.00 |
| [][]byte 10×1000 (separate cells): xs[0][0] = v | 0.0230 | 0.0224..0.0232 | 0.01 | 0.0029 | 29.00 |

**(d) allocation-only loops** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `alloc_new(1000,)` | 0.0455 | 0.0444..0.0475 | 0.04 | 0.0254 | 25.40 |
| `alloc_new(4000,)` | 0.1167 | 0.1166..0.1262 | 0.11 | 0.0966 | 24.15 |
| `alloc_new(16000,)` | 0.4541 | 0.4396..0.4825 | 0.44 | 0.4340 | 27.12 |
| `alloc_new(32000,)` | 0.8853 | 0.8525..0.8889 | 0.87 | 0.8652 | 27.04 |

successive net ratios — 1000→4000: ×3.80 (linear ×4.0, quadratic ×16.0, cubic ×64.0); 4000→16000: ×4.49 (linear ×4.0, quadratic ×16.0, cubic ×64.0); 16000→32000: ×1.99 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(d′) `make([]byte, 4)` per iteration (the 2026-09-03 audit probe)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `alloc_make4(1000,)` | 0.0426 | 0.0425..0.0431 | 0.03 | 0.0225 | 22.50 |
| `alloc_make4(4000,)` | 0.1146 | 0.1066..0.1159 | 0.10 | 0.0945 | 23.62 |
| `alloc_make4(16000,)` | 0.3856 | 0.3762..0.4051 | 0.38 | 0.3655 | 22.84 |

successive net ratios — 1000→4000: ×4.20 (linear ×4.0, quadratic ×16.0, cubic ×64.0); 4000→16000: ×3.87 (linear ×4.0, quadratic ×16.0, cubic ×64.0)

**(h) live-heap size h vs a fixed 20,000-iteration scalar loop — allocation phase alone (w = 0)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_scalar(0, 0)` | 0.0196 | 0.0194..0.0197 | 0.01 | -0.0005 | — |
| `heap_then_scalar(1000, 0)` | 0.0402 | 0.0389..0.0412 | 0.03 | 0.0201 | 20.10 |
| `heap_then_scalar(10000, 0)` | 0.2192 | 0.2178..0.2203 | 0.21 | 0.1991 | 19.91 |
| `heap_then_scalar(40000, 0)` | 0.8682 | 0.8141..0.8937 | 0.86 | 0.8481 | 21.20 |

successive net ratios — 1000→10000: ×9.91 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 10000→40000: ×4.26 (linear ×4.0, quadratic ×16.0, cubic ×64.0)

**(h) … allocation phase + scalar phase (w = 20000)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_scalar(0, 20000)` | 0.3026 | 0.2889..0.3035 | 0.29 | 0.2825 | 14.12 |
| `heap_then_scalar(1000, 20000)` | 0.3257 | 0.3063..0.3383 | 0.32 | 0.3056 | 15.28 |
| `heap_then_scalar(10000, 20000)` | 0.4892 | 0.4876..0.5072 | 0.48 | 0.4691 | 23.46 |
| `heap_then_scalar(40000, 20000)` | 1.1319 | 1.1074..1.1486 | 1.12 | 1.1118 | 55.59 |

scalar-phase cost at heap size h (= (h, 20000) net − (h, 0) net):
  h=0: 0.2830 s
  h=1000: 0.2855 s
  h=10000: 0.2700 s
  h=40000: 0.2637 s

**(h′) live-heap size h vs 300 in-place appends — allocation phase alone (w = 0)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_append(0, 0)` | 0.0197 | 0.0192..0.0212 | 0.01 | -0.0004 | — |
| `heap_then_append(10000, 0)` | 0.2360 | 0.2179..0.2368 | 0.23 | 0.2159 | 21.59 |
| `heap_then_append(40000, 0)` | 0.8671 | 0.8400..0.8867 | 0.86 | 0.8470 | 21.18 |

**(h′) … + 300 in-place appends (w = 300)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_append(0, 300)` | 0.0278 | 0.0272..0.0286 | 0.02 | 0.0077 | 25.67 |
| `heap_then_append(10000, 300)` | 0.2403 | 0.2364..0.2405 | 0.23 | 0.2202 | 734.00 |
| `heap_then_append(40000, 300)` | 0.8259 | 0.8230..0.8657 | 0.82 | 0.8058 | 2686.00 |

append-phase cost at heap size h (= (h, 300) net − (h, 0) net):
  h=0: 0.0081 s
  h=10000: 0.0043 s
  h=40000: -0.0412 s

**(g) map writes, n distinct int keys** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `map_write(500,)` | 0.0279 | 0.0276..0.0292 | 0.02 | 0.0078 | 15.60 |
| `map_write(1000,)` | 0.0412 | 0.0397..0.0421 | 0.03 | 0.0211 | 21.10 |
| `map_write(2000,)` | 0.0801 | 0.0784..0.0844 | 0.07 | 0.0600 | 30.00 |
| `map_write(4000,)` | 0.2073 | 0.2060..0.2078 | 0.20 | 0.1872 | 46.80 |

successive net ratios — 500→1000: ×2.71 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1000→2000: ×2.84 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 2000→4000: ×3.12 (linear ×2.0, quadratic ×4.0, cubic ×8.0)
