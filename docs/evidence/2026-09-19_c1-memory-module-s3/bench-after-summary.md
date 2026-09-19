commit 0f114df68e41cc5e40f14274f98af608fd7a5596  golean sha256 12ebb0e1202b8b43…  go version go1.26.5 linux/amd64  nproc 32  load1 start 1.86 end 2.31  started 2026-09-19T06:37:17Z

empty probe (startup): median 0.0191 s over 7 runs [0.0184..0.0199], rss 72892 KB

steps per loop iteration (fuel bisection): alloc_new=85, append_cap=84, append_grow=84, heap_then_scalar=70, heap_then_scalar=49, map_write=44, read_fixed=55, scalar=49, struct_arr_100=47, write_fixed=51

**(e) scalar loop — per-step baseline** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `scalar(10000,)` | 0.1626 | 0.1541..0.1753 | 0.15 | 0.1435 | 14.35 |
| `scalar(20000,)` | 0.2991 | 0.2956..0.3222 | 0.29 | 0.2800 | 14.00 |
| `scalar(40000,)` | 0.5609 | 0.5412..0.5813 | 0.55 | 0.5418 | 13.54 |
| `scalar(80000,)` | 1.0765 | 1.0645..1.1669 | 1.06 | 1.0574 | 13.22 |

successive net ratios — 10000→20000: ×1.95 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 20000→40000: ×1.94 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 40000→80000: ×1.95 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

per machine step at n=80000: 270 ns (49 steps/iteration)

**(a) the review's loop: `append` growing from nil** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `append_grow(250,)` | 0.0276 | 0.0266..0.0285 | 0.02 | 0.0085 | 34.00 |
| `append_grow(500,)` | 0.0355 | 0.0332..0.0366 | 0.03 | 0.0164 | 32.80 |
| `append_grow(1000,)` | 0.0523 | 0.0488..0.0601 | 0.04 | 0.0332 | 33.20 |
| `append_grow(2000,)` | 0.0803 | 0.0793..0.0836 | 0.07 | 0.0612 | 30.60 |
| `append_grow(4000,)` | 0.1395 | 0.1377..0.1515 | 0.13 | 0.1204 | 30.10 |

successive net ratios — 250→500: ×1.93 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 500→1000: ×2.02 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1000→2000: ×1.84 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 2000→4000: ×1.97 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(f) in-place `append`, w = c (no spill)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `append_cap(250, 250)` | 0.0260 | 0.0259..0.0276 | 0.02 | 0.0069 | 27.60 |
| `append_cap(500, 500)` | 0.0351 | 0.0338..0.0377 | 0.03 | 0.0160 | 32.00 |
| `append_cap(1000, 1000)` | 0.0498 | 0.0472..0.0510 | 0.04 | 0.0307 | 30.70 |
| `append_cap(2000, 2000)` | 0.0784 | 0.0782..0.0798 | 0.07 | 0.0593 | 29.65 |

successive net ratios — 250→500: ×2.32 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 500→1000: ×1.92 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1000→2000: ×1.93 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(f′) 100 in-place appends, capacity c varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `append_cap(100, 100)` | 0.0227 | 0.0213..0.0231 | 0.01 | 0.0036 | 36.00 |
| `append_cap(200, 100)` | 0.0216 | 0.0214..0.0227 | 0.01 | 0.0025 | 25.00 |
| `append_cap(400, 100)` | 0.0228 | 0.0217..0.0240 | 0.01 | 0.0037 | 37.00 |
| `append_cap(800, 100)` | 0.0219 | 0.0217..0.0236 | 0.01 | 0.0028 | 28.00 |
| `append_cap(1600, 100)` | 0.0235 | 0.0224..0.0240 | 0.01 | 0.0044 | 44.00 |
| `append_cap(3200, 100)` | 0.0235 | 0.0219..0.0255 | 0.01 | 0.0044 | 44.00 |
| `append_cap(6400, 100)` | 0.0232 | 0.0229..0.0245 | 0.01 | 0.0041 | 41.00 |

successive net ratios — 100→200: ×0.69 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 200→400: ×1.48 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 400→800: ×0.76 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 800→1600: ×1.57 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1600→3200: ×1.00 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 3200→6400: ×0.93 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(b) 100 element writes `xs[0] = v`, slice length m varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `write_fixed(10, 100)` | 0.0212 | 0.0200..0.0222 | 0.01 | 0.0021 | 21.00 |
| `write_fixed(100, 100)` | 0.0224 | 0.0222..0.0224 | 0.01 | 0.0033 | 33.00 |
| `write_fixed(1000, 100)` | 0.0225 | 0.0216..0.0231 | 0.01 | 0.0034 | 34.00 |
| `write_fixed(3000, 100)` | 0.0223 | 0.0223..0.0225 | 0.01 | 0.0032 | 32.00 |
| `write_fixed(10000, 100)` | 0.0234 | 0.0223..0.0242 | 0.01 | 0.0043 | 43.00 |

successive net ratios — 10→100: ×1.57 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 100→1000: ×1.03 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 1000→3000: ×0.94 (linear ×3.0, quadratic ×9.0, cubic ×27.0); 3000→10000: ×1.34 (linear ×3.3, quadratic ×11.1, cubic ×37.0)

**(b′) element writes at m = 10, write count varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `write_fixed(10, 100)` | 0.0212 | 0.0200..0.0222 | 0.01 | 0.0021 | 21.00 |
| `write_fixed(10, 1000)` | 0.0349 | 0.0348..0.0361 | 0.03 | 0.0158 | 15.80 |
| `write_fixed(10, 10000)` | 0.1704 | 0.1607..0.1718 | 0.16 | 0.1513 | 15.13 |

successive net ratios — 100→1000: ×7.52 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 1000→10000: ×9.58 (linear ×10.0, quadratic ×100.0, cubic ×1000.0)

**(i) 1,000 element reads `xs[0]`, slice length m varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `read_fixed(10, 1000)` | 0.0368 | 0.0368..0.0384 | 0.03 | 0.0177 | 17.70 |
| `read_fixed(100, 1000)` | 0.0366 | 0.0361..0.0368 | 0.03 | 0.0175 | 17.50 |
| `read_fixed(1000, 1000)` | 0.0370 | 0.0363..0.0371 | 0.03 | 0.0179 | 17.90 |
| `read_fixed(10000, 1000)` | 0.0363 | 0.0358..0.0374 | 0.03 | 0.0172 | 17.20 |

successive net ratios — 10→100: ×0.99 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 100→1000: ×1.02 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 1000→10000: ×0.96 (linear ×10.0, quadratic ×100.0, cubic ×1000.0)

**(c) aggregate shape — 100 writes each** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| struct{y,x int}: s.x = i | 0.0202 | 0.0197..0.0217 | 0.01 | 0.0011 | 11.00 |
| struct{a [100]byte; x int}: s.x = i | 0.0210 | 0.0202..0.0222 | 0.01 | 0.0019 | 19.00 |
| struct{a [1000]byte; x int}: s.x = i | 0.0224 | 0.0205..0.0231 | 0.01 | 0.0033 | 33.00 |
| struct{a [10000]byte; x int}: s.x = i | 0.0232 | 0.0211..0.0234 | 0.01 | 0.0041 | 41.00 |
| struct{a []byte; x int}, len(a)=100: s.x = i | 0.0221 | 0.0213..0.0224 | 0.01 | 0.0030 | 30.00 |
| struct{a []byte; x int}, len(a)=10000: s.x = i | 0.0228 | 0.0217..0.0231 | 0.01 | 0.0037 | 37.00 |
| [10000]byte: b[0] = v | 0.0236 | 0.0233..0.0249 | 0.01 | 0.0045 | 45.00 |
| [10][1000]byte: a[0][0] = v | 0.0215 | 0.0210..0.0230 | 0.01 | 0.0024 | 24.00 |
| [100][100]byte: a[0][0] = v | 0.0212 | 0.0211..0.0212 | 0.01 | 0.0021 | 21.00 |
| [][]byte 10×1000 (separate cells): xs[0][0] = v | 0.0219 | 0.0213..0.0221 | 0.01 | 0.0028 | 28.00 |

**(d) allocation-only loops** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `alloc_new(1000,)` | 0.0445 | 0.0435..0.0458 | 0.04 | 0.0254 | 25.40 |
| `alloc_new(4000,)` | 0.1180 | 0.1177..0.1260 | 0.11 | 0.0989 | 24.72 |
| `alloc_new(16000,)` | 0.4480 | 0.4397..0.4623 | 0.44 | 0.4289 | 26.81 |
| `alloc_new(32000,)` | 0.8635 | 0.8609..0.8808 | 0.85 | 0.8444 | 26.39 |

successive net ratios — 1000→4000: ×3.89 (linear ×4.0, quadratic ×16.0, cubic ×64.0); 4000→16000: ×4.34 (linear ×4.0, quadratic ×16.0, cubic ×64.0); 16000→32000: ×1.97 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(d′) `make([]byte, 4)` per iteration (the 2026-09-03 audit probe)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `alloc_make4(1000,)` | 0.0451 | 0.0427..0.0466 | 0.04 | 0.0260 | 26.00 |
| `alloc_make4(4000,)` | 0.1199 | 0.1159..0.1199 | 0.11 | 0.1008 | 25.20 |
| `alloc_make4(16000,)` | 0.4004 | 0.3797..0.4056 | 0.39 | 0.3813 | 23.83 |

successive net ratios — 1000→4000: ×3.88 (linear ×4.0, quadratic ×16.0, cubic ×64.0); 4000→16000: ×3.78 (linear ×4.0, quadratic ×16.0, cubic ×64.0)

**(h) live-heap size h vs a fixed 20,000-iteration scalar loop — allocation phase alone (w = 0)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_scalar(0, 0)` | 0.0223 | 0.0188..0.0238 | 0.01 | 0.0032 | — |
| `heap_then_scalar(1000, 0)` | 0.0416 | 0.0407..0.0419 | 0.03 | 0.0225 | 22.50 |
| `heap_then_scalar(10000, 0)` | 0.2332 | 0.2315..0.2404 | 0.22 | 0.2141 | 21.41 |
| `heap_then_scalar(40000, 0)` | 0.8685 | 0.8296..0.8733 | 0.86 | 0.8494 | 21.24 |

successive net ratios — 1000→10000: ×9.52 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 10000→40000: ×3.97 (linear ×4.0, quadratic ×16.0, cubic ×64.0)

**(h) … allocation phase + scalar phase (w = 20000)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_scalar(0, 20000)` | 0.2790 | 0.2788..0.2835 | 0.27 | 0.2599 | 13.00 |
| `heap_then_scalar(1000, 20000)` | 0.3077 | 0.3050..0.3592 | 0.30 | 0.2886 | 14.43 |
| `heap_then_scalar(10000, 20000)` | 0.5206 | 0.5168..0.5256 | 0.51 | 0.5015 | 25.07 |
| `heap_then_scalar(40000, 20000)` | 1.1574 | 1.1038..1.1662 | 1.15 | 1.1383 | 56.92 |

scalar-phase cost at heap size h (= (h, 20000) net − (h, 0) net):
  h=0: 0.2567 s
  h=1000: 0.2661 s
  h=10000: 0.2874 s
  h=40000: 0.2889 s

**(h′) live-heap size h vs 300 in-place appends — allocation phase alone (w = 0)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_append(0, 0)` | 0.0197 | 0.0194..0.0204 | 0.01 | 0.0006 | — |
| `heap_then_append(10000, 0)` | 0.2276 | 0.2197..0.2350 | 0.22 | 0.2085 | 20.85 |
| `heap_then_append(40000, 0)` | 0.8491 | 0.8287..0.8560 | 0.84 | 0.8300 | 20.75 |

**(h′) … + 300 in-place appends (w = 300)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_append(0, 300)` | 0.0277 | 0.0270..0.0280 | 0.02 | 0.0086 | 28.67 |
| `heap_then_append(10000, 300)` | 0.2372 | 0.2316..0.2378 | 0.23 | 0.2181 | 727.00 |
| `heap_then_append(40000, 300)` | 0.8394 | 0.8303..0.8712 | 0.83 | 0.8203 | 2734.33 |

append-phase cost at heap size h (= (h, 300) net − (h, 0) net):
  h=0: 0.0080 s
  h=10000: 0.0096 s
  h=40000: -0.0097 s

**(g) map writes, n distinct int keys** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `map_write(500,)` | 0.0290 | 0.0284..0.0302 | 0.02 | 0.0099 | 19.80 |
| `map_write(1000,)` | 0.0415 | 0.0403..0.0434 | 0.03 | 0.0224 | 22.40 |
| `map_write(2000,)` | 0.0784 | 0.0782..0.0821 | 0.07 | 0.0593 | 29.65 |
| `map_write(4000,)` | 0.2078 | 0.2050..0.2085 | 0.20 | 0.1887 | 47.18 |

successive net ratios — 500→1000: ×2.26 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1000→2000: ×2.65 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 2000→4000: ×3.18 (linear ×2.0, quadratic ×4.0, cubic ×8.0)
