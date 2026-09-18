commit a8ada3ccd97793857b83a476e184ddde7a3bfbc6  golean sha256 231df9a99f459d4a…  go version go1.26.5 linux/amd64  nproc 32  load1 start 3.35 end 1.48  started 2026-09-18T18:53:23Z

empty probe (startup): median 0.0216 s over 7 runs [0.0207..0.0222], rss 68112 KB

steps per loop iteration (fuel bisection): alloc_new=85, append_cap=84, append_grow=84, heap_then_scalar=70, heap_then_scalar=49, map_write=44, read_fixed=55, scalar=49, struct_arr_100=47, write_fixed=51

**(e) scalar loop — per-step baseline** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `scalar(10000,)` | 0.1620 | 0.1517..0.1637 | 0.15 | 0.1404 | 14.04 |
| `scalar(20000,)` | 0.3026 | 0.2857..0.3055 | 0.29 | 0.2810 | 14.05 |
| `scalar(40000,)` | 0.5816 | 0.5775..0.5901 | 0.57 | 0.5600 | 14.00 |
| `scalar(80000,)` | 1.0981 | 1.0618..1.1355 | 1.08 | 1.0765 | 13.46 |

successive net ratios — 10000→20000: ×2.00 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 20000→40000: ×1.99 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 40000→80000: ×1.92 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

per machine step at n=80000: 275 ns (49 steps/iteration)

**(a) the review's loop: `append` growing from nil** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `append_grow(250,)` | 0.0443 | 0.0440..0.0451 | 0.03 | 0.0227 | 90.80 |
| `append_grow(500,)` | 0.1324 | 0.1316..0.1398 | 0.12 | 0.1108 | 221.60 |
| `append_grow(1000,)` | 0.7318 | 0.6946..0.7397 | 0.72 | 0.7102 | 710.20 |
| `append_grow(2000,)` | 4.4859 | 4.4610..4.5598 | 4.47 | 4.4643 | 2232.15 |
| `append_grow(4000,)` | 31.0902 | 31.0877..31.3490 | 31.07 | 31.0686 | 7767.15 |

successive net ratios — 250→500: ×4.88 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 500→1000: ×6.41 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1000→2000: ×6.29 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 2000→4000: ×6.96 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(f) in-place `append`, w = c (no spill)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `append_cap(250, 250)` | (not run) | | | | |
| `append_cap(500, 500)` | (not run) | | | | |
| `append_cap(1000, 1000)` | (not run) | | | | |
| `append_cap(2000, 2000)` | (not run) | | | | |

**(f′) 100 in-place appends, capacity c varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `append_cap(100, 100)` | (not run) | | | | |
| `append_cap(200, 100)` | (not run) | | | | |
| `append_cap(400, 100)` | (not run) | | | | |
| `append_cap(800, 100)` | (not run) | | | | |
| `append_cap(1600, 100)` | (not run) | | | | |
| `append_cap(3200, 100)` | (not run) | | | | |
| `append_cap(6400, 100)` | (not run) | | | | |

**(b) 100 element writes `xs[0] = v`, slice length m varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `write_fixed(10, 100)` | 0.0242 | 0.0235..0.0243 | 0.01 | 0.0026 | 26.00 |
| `write_fixed(100, 100)` | 0.0263 | 0.0263..0.0266 | 0.01 | 0.0047 | 47.00 |
| `write_fixed(1000, 100)` | 0.1409 | 0.1379..0.1456 | 0.13 | 0.1193 | 1193.00 |
| `write_fixed(3000, 100)` | 1.0096 | 1.0081..1.0127 | 1.00 | 0.9880 | 9880.00 |
| `write_fixed(10000, 100)` | 10.8298 | 10.8178..10.9226 | 10.82 | 10.8082 | 108082.00 |

successive net ratios — 10→100: ×1.81 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 100→1000: ×25.38 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 1000→3000: ×8.28 (linear ×3.0, quadratic ×9.0, cubic ×27.0); 3000→10000: ×10.94 (linear ×3.3, quadratic ×11.1, cubic ×37.0)

**(b′) element writes at m = 10, write count varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `write_fixed(10, 100)` | 0.0242 | 0.0235..0.0243 | 0.01 | 0.0026 | 26.00 |
| `write_fixed(10, 1000)` | 0.0399 | 0.0395..0.0404 | 0.03 | 0.0183 | 18.30 |
| `write_fixed(10, 10000)` | 0.1839 | 0.1829..0.1895 | 0.18 | 0.1623 | 16.23 |

successive net ratios — 100→1000: ×7.04 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 1000→10000: ×8.87 (linear ×10.0, quadratic ×100.0, cubic ×1000.0)

**(i) 1,000 element reads `xs[0]`, slice length m varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `read_fixed(10, 1000)` | 0.0459 | 0.0452..0.0495 | 0.03 | 0.0243 | 24.30 |
| `read_fixed(100, 1000)` | 0.0441 | 0.0438..0.0487 | 0.03 | 0.0225 | 22.50 |
| `read_fixed(1000, 1000)` | 0.0439 | 0.0414..0.0455 | 0.03 | 0.0223 | 22.30 |
| `read_fixed(10000, 1000)` | 0.0392 | 0.0384..0.0407 | 0.03 | 0.0176 | 17.60 |

successive net ratios — 10→100: ×0.93 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 100→1000: ×0.99 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 1000→10000: ×0.79 (linear ×10.0, quadratic ×100.0, cubic ×1000.0)

**(c) aggregate shape — 100 writes each** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| struct{y,x int}: s.x = i | (not run) | | | | |
| struct{a [100]byte; x int}: s.x = i | (not run) | | | | |
| struct{a [1000]byte; x int}: s.x = i | (not run) | | | | |
| struct{a [10000]byte; x int}: s.x = i | (not run) | | | | |
| struct{a []byte; x int}, len(a)=100: s.x = i | (not run) | | | | |
| struct{a []byte; x int}, len(a)=10000: s.x = i | (not run) | | | | |
| [10000]byte: b[0] = v | (not run) | | | | |
| [10][1000]byte: a[0][0] = v | (not run) | | | | |
| [100][100]byte: a[0][0] = v | (not run) | | | | |
| [][]byte 10×1000 (separate cells): xs[0][0] = v | (not run) | | | | |

**(d) allocation-only loops** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `alloc_new(1000,)` | 0.0609 | 0.0587..0.0623 | 0.05 | 0.0393 | 39.30 |
| `alloc_new(4000,)` | 0.2830 | 0.2754..0.2877 | 0.27 | 0.2614 | 65.35 |
| `alloc_new(16000,)` | 3.5239 | 3.5185..3.6642 | 3.51 | 3.5023 | 218.89 |
| `alloc_new(32000,)` | 13.8698 | 13.6376..15.6687 | 13.86 | 13.8482 | 432.76 |

successive net ratios — 1000→4000: ×6.65 (linear ×4.0, quadratic ×16.0, cubic ×64.0); 4000→16000: ×13.40 (linear ×4.0, quadratic ×16.0, cubic ×64.0); 16000→32000: ×3.95 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(d′) `make([]byte, 4)` per iteration (the 2026-09-03 audit probe)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `alloc_make4(1000,)` | (not run) | | | | |
| `alloc_make4(4000,)` | (not run) | | | | |
| `alloc_make4(16000,)` | (not run) | | | | |

**(h) live-heap size h vs a fixed 20,000-iteration scalar loop — allocation phase alone (w = 0)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_scalar(0, 0)` | 0.0242 | 0.0226..0.0245 | 0.01 | 0.0026 | — |
| `heap_then_scalar(1000, 0)` | 0.0575 | 0.0565..0.0578 | 0.04 | 0.0359 | 35.90 |
| `heap_then_scalar(10000, 0)` | 1.3234 | 1.3148..1.3384 | 1.31 | 1.3018 | 130.18 |
| `heap_then_scalar(40000, 0)` | 18.6144 | 18.4085..19.3872 | 18.60 | 18.5928 | 464.82 |

successive net ratios — 1000→10000: ×36.26 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 10000→40000: ×14.28 (linear ×4.0, quadratic ×16.0, cubic ×64.0)

**(h) … allocation phase + scalar phase (w = 20000)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_scalar(0, 20000)` | 0.2938 | 0.2858..0.3094 | 0.28 | 0.2722 | 13.61 |
| `heap_then_scalar(1000, 20000)` | 0.4305 | 0.4300..0.4516 | 0.42 | 0.4089 | 20.44 |
| `heap_then_scalar(10000, 20000)` | 3.0005 | 2.9557..3.0746 | 2.99 | 2.9789 | 148.95 |
| `heap_then_scalar(40000, 20000)` | 23.9580 | 23.7853..24.1101 | 23.94 | 23.9364 | 1196.82 |

scalar-phase cost at heap size h (= (h, 20000) net − (h, 0) net):
  h=0: 0.2696 s
  h=1000: 0.3730 s
  h=10000: 1.6771 s
  h=40000: 5.3436 s

**(h′) live-heap size h vs 300 in-place appends — allocation phase alone (w = 0)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_append(0, 0)` | (not run) | | | | |
| `heap_then_append(10000, 0)` | (not run) | | | | |
| `heap_then_append(40000, 0)` | (not run) | | | | |

**(h′) … + 300 in-place appends (w = 300)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_append(0, 300)` | (not run) | | | | |
| `heap_then_append(10000, 300)` | (not run) | | | | |
| `heap_then_append(40000, 300)` | (not run) | | | | |

append-phase cost at heap size h (= (h, 300) net − (h, 0) net):

**(g) map writes, n distinct int keys** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `map_write(500,)` | (not run) | | | | |
| `map_write(1000,)` | (not run) | | | | |
| `map_write(2000,)` | (not run) | | | | |
| `map_write(4000,)` | (not run) | | | | |
