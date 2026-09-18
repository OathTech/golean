commit 50f293d9751444073ddeea90d6bec0adfa74ada3  golean sha256 f462cf50f2015462…  go version go1.26.5 linux/amd64  nproc 32  load1 start 2.06 end 1.15  started 2026-09-18T09:18:11Z

empty probe (startup): median 0.0213 s over 7 runs [0.0204..0.0214], rss 72472 KB

steps per loop iteration (fuel bisection): alloc_new=85, append_cap=84, append_grow=84, heap_then_scalar=70, heap_then_scalar=49, map_write=44, read_fixed=55, scalar=49, struct_arr_100=47, write_fixed=51

**(e) scalar loop — per-step baseline** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `scalar(10000,)` | 0.1598 | 0.1390..0.1649 | 0.15 | 0.1385 | 13.85 |
| `scalar(20000,)` | 0.2612 | 0.2571..0.2822 | 0.25 | 0.2399 | 11.99 |
| `scalar(40000,)` | 0.4791 | 0.4774..0.4882 | 0.47 | 0.4578 | 11.45 |
| `scalar(80000,)` | 1.0227 | 0.9543..1.0291 | 1.01 | 1.0014 | 12.52 |

successive net ratios — 10000→20000: ×1.73 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 20000→40000: ×1.91 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 40000→80000: ×2.19 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

per machine step at n=80000: 255 ns (49 steps/iteration)

**(a) the review's loop: `append` growing from nil** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `append_grow(250,)` | 0.0269 | 0.0267..0.0271 | 0.02 | 0.0056 | 22.40 |
| `append_grow(500,)` | 0.0354 | 0.0351..0.0369 | 0.03 | 0.0141 | 28.20 |
| `append_grow(1000,)` | 0.0565 | 0.0554..0.0626 | 0.04 | 0.0352 | 35.20 |
| `append_grow(2000,)` | 0.1214 | 0.1116..0.1281 | 0.11 | 0.1001 | 50.05 |
| `append_grow(4000,)` | 0.2961 | 0.2897..0.2972 | 0.28 | 0.2748 | 68.70 |

successive net ratios — 250→500: ×2.52 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 500→1000: ×2.50 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1000→2000: ×2.84 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 2000→4000: ×2.75 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(f) in-place `append`, w = c (no spill)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `append_cap(250, 250)` | 0.0273 | 0.0265..0.0278 | 0.02 | 0.0060 | 24.00 |
| `append_cap(500, 500)` | 0.0368 | 0.0352..0.0370 | 0.03 | 0.0155 | 31.00 |
| `append_cap(1000, 1000)` | 0.0623 | 0.0604..0.0628 | 0.05 | 0.0410 | 41.00 |
| `append_cap(2000, 2000)` | 0.1180 | 0.1131..0.1225 | 0.11 | 0.0967 | 48.35 |

successive net ratios — 250→500: ×2.58 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 500→1000: ×2.65 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1000→2000: ×2.36 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(f′) 100 in-place appends, capacity c varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `append_cap(100, 100)` | 0.0226 | 0.0225..0.0228 | 0.01 | 0.0013 | 13.00 |
| `append_cap(200, 100)` | 0.0217 | 0.0216..0.0219 | 0.01 | 0.0004 | 4.00 |
| `append_cap(400, 100)` | 0.0217 | 0.0215..0.0220 | 0.01 | 0.0004 | 4.00 |
| `append_cap(800, 100)` | 0.0228 | 0.0219..0.0228 | 0.01 | 0.0015 | 15.00 |
| `append_cap(1600, 100)` | 0.0222 | 0.0219..0.0226 | 0.01 | 0.0009 | 9.00 |
| `append_cap(3200, 100)` | 0.0230 | 0.0229..0.0238 | 0.01 | 0.0017 | 17.00 |
| `append_cap(6400, 100)` | 0.0242 | 0.0241..0.0250 | 0.02 | 0.0029 | 29.00 |

**(b) 100 element writes `xs[0] = v`, slice length m varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `write_fixed(10, 100)` | 0.0211 | 0.0211..0.0213 | 0.01 | -0.0002 | -2.00 |
| `write_fixed(100, 100)` | 0.0214 | 0.0210..0.0220 | 0.01 | 0.0001 | 1.00 |
| `write_fixed(1000, 100)` | 0.0216 | 0.0214..0.0220 | 0.01 | 0.0003 | 3.00 |
| `write_fixed(3000, 100)` | 0.0211 | 0.0207..0.0225 | 0.01 | -0.0002 | -2.00 |
| `write_fixed(10000, 100)` | 0.0229 | 0.0225..0.0246 | 0.01 | 0.0016 | 16.00 |

**(b′) element writes at m = 10, write count varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `write_fixed(10, 100)` | 0.0211 | 0.0211..0.0213 | 0.01 | -0.0002 | -2.00 |
| `write_fixed(10, 1000)` | 0.0344 | 0.0333..0.0345 | 0.02 | 0.0131 | 13.10 |
| `write_fixed(10, 10000)` | 0.1470 | 0.1458..0.1576 | 0.14 | 0.1257 | 12.57 |

successive net ratios — 1000→10000: ×9.60 (linear ×10.0, quadratic ×100.0, cubic ×1000.0)

**(i) 1,000 element reads `xs[0]`, slice length m varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `read_fixed(10, 1000)` | 0.0381 | 0.0336..0.0381 | 0.03 | 0.0168 | 16.80 |
| `read_fixed(100, 1000)` | 0.0374 | 0.0370..0.0388 | 0.03 | 0.0161 | 16.10 |
| `read_fixed(1000, 1000)` | 0.0393 | 0.0363..0.0395 | 0.03 | 0.0180 | 18.00 |
| `read_fixed(10000, 1000)` | 0.0380 | 0.0376..0.0381 | 0.03 | 0.0167 | 16.70 |

successive net ratios — 10→100: ×0.96 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 100→1000: ×1.12 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 1000→10000: ×0.93 (linear ×10.0, quadratic ×100.0, cubic ×1000.0)

**(c) aggregate shape — 100 writes each** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| struct{y,x int}: s.x = i | 0.0215 | 0.0207..0.0226 | 0.01 | 0.0002 | 2.00 |
| struct{a [100]byte; x int}: s.x = i | 0.0207 | 0.0202..0.0213 | 0.01 | -0.0006 | -6.00 |
| struct{a [1000]byte; x int}: s.x = i | 0.0213 | 0.0207..0.0214 | 0.01 | 0.0000 | 0.00 |
| struct{a [10000]byte; x int}: s.x = i | 0.0218 | 0.0209..0.0227 | 0.01 | 0.0005 | 5.00 |
| struct{a []byte; x int}, len(a)=100: s.x = i | 0.0202 | 0.0194..0.0214 | 0.01 | -0.0011 | -11.00 |
| struct{a []byte; x int}, len(a)=10000: s.x = i | 0.0223 | 0.0211..0.0223 | 0.01 | 0.0010 | 10.00 |
| [10000]byte: b[0] = v | 0.0236 | 0.0232..0.0236 | 0.01 | 0.0023 | 23.00 |
| [10][1000]byte: a[0][0] = v | 0.0215 | 0.0208..0.0226 | 0.01 | 0.0002 | 2.00 |
| [100][100]byte: a[0][0] = v | 0.0225 | 0.0210..0.0231 | 0.01 | 0.0012 | 12.00 |
| [][]byte 10×1000 (separate cells): xs[0][0] = v | 0.0212 | 0.0210..0.0218 | 0.01 | -0.0001 | -1.00 |

**(d) allocation-only loops** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `alloc_new(1000,)` | 0.0552 | 0.0541..0.0571 | 0.05 | 0.0339 | 33.90 |
| `alloc_new(4000,)` | 0.2810 | 0.2744..0.3045 | 0.27 | 0.2597 | 64.93 |
| `alloc_new(16000,)` | 3.5287 | 3.5220..3.7267 | 3.52 | 3.5074 | 219.21 |
| `alloc_new(32000,)` | 13.5264 | 13.2313..13.7272 | 13.51 | 13.5051 | 422.03 |

successive net ratios — 1000→4000: ×7.66 (linear ×4.0, quadratic ×16.0, cubic ×64.0); 4000→16000: ×13.51 (linear ×4.0, quadratic ×16.0, cubic ×64.0); 16000→32000: ×3.85 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(d′) `make([]byte, 4)` per iteration (the 2026-09-03 audit probe)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `alloc_make4(1000,)` | 0.0549 | 0.0511..0.0551 | 0.04 | 0.0336 | 33.60 |
| `alloc_make4(4000,)` | 0.2689 | 0.2624..0.2696 | 0.26 | 0.2476 | 61.90 |
| `alloc_make4(16000,)` | 3.6225 | 3.5911..3.6262 | 3.61 | 3.6012 | 225.08 |

successive net ratios — 1000→4000: ×7.37 (linear ×4.0, quadratic ×16.0, cubic ×64.0); 4000→16000: ×14.54 (linear ×4.0, quadratic ×16.0, cubic ×64.0)

**(h) live-heap size h vs a fixed 20,000-iteration scalar loop — allocation phase alone (w = 0)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_scalar(0, 0)` | 0.0193 | 0.0187..0.0199 | 0.01 | -0.0020 | — |
| `heap_then_scalar(1000, 0)` | 0.0490 | 0.0476..0.0516 | 0.04 | 0.0277 | 27.70 |
| `heap_then_scalar(10000, 0)` | 1.2339 | 1.2234..1.2553 | 1.22 | 1.2126 | 121.26 |
| `heap_then_scalar(40000, 0)` | 18.1657 | 17.8454..18.3528 | 18.15 | 18.1444 | 453.61 |

successive net ratios — 1000→10000: ×43.78 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 10000→40000: ×14.96 (linear ×4.0, quadratic ×16.0, cubic ×64.0)

**(h) … allocation phase + scalar phase (w = 20000)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_scalar(0, 20000)` | 0.2786 | 0.2606..0.2818 | 0.27 | 0.2573 | 12.87 |
| `heap_then_scalar(1000, 20000)` | 0.4338 | 0.3994..0.4378 | 0.42 | 0.4125 | 20.63 |
| `heap_then_scalar(10000, 20000)` | 3.1185 | 3.0872..3.1727 | 3.11 | 3.0972 | 154.86 |
| `heap_then_scalar(40000, 20000)` | 24.2205 | 24.0471..24.4957 | 24.21 | 24.1992 | 1209.96 |

scalar-phase cost at heap size h (= (h, 20000) net − (h, 0) net):
  h=0: 0.2593 s
  h=1000: 0.3848 s
  h=10000: 1.8846 s
  h=40000: 6.0548 s

**(h′) live-heap size h vs 300 in-place appends — allocation phase alone (w = 0)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_append(0, 0)` | 0.0188 | 0.0185..0.0205 | 0.01 | -0.0025 | — |
| `heap_then_append(10000, 0)` | 1.2677 | 1.2653..1.2805 | 1.26 | 1.2464 | 124.64 |
| `heap_then_append(40000, 0)` | 18.2680 | 18.0524..18.3260 | 18.25 | 18.2467 | 456.17 |

**(h′) … + 300 in-place appends (w = 300)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_append(0, 300)` | 0.0285 | 0.0285..0.0289 | 0.02 | 0.0072 | 24.00 |
| `heap_then_append(10000, 300)` | 1.3456 | 1.3453..1.3733 | 1.33 | 1.3243 | 4414.33 |
| `heap_then_append(40000, 300)` | 18.5141 | 18.2535..18.7330 | 18.50 | 18.4928 | 61642.67 |

append-phase cost at heap size h (= (h, 300) net − (h, 0) net):
  h=0: 0.0097 s
  h=10000: 0.0779 s
  h=40000: 0.2461 s

**(g) map writes, n distinct int keys** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `map_write(500,)` | 0.0278 | 0.0277..0.0286 | 0.02 | 0.0065 | 13.00 |
| `map_write(1000,)` | 0.0412 | 0.0393..0.0412 | 0.03 | 0.0199 | 19.90 |
| `map_write(2000,)` | 0.0813 | 0.0754..0.0821 | 0.07 | 0.0600 | 30.00 |
| `map_write(4000,)` | 0.2000 | 0.1999..0.2043 | 0.19 | 0.1787 | 44.68 |

successive net ratios — 500→1000: ×3.06 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1000→2000: ×3.02 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 2000→4000: ×2.98 (linear ×2.0, quadratic ×4.0, cubic ×8.0)
