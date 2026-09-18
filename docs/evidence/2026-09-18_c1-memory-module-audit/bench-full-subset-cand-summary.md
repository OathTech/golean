commit a8ada3ccd97793857b83a476e184ddde7a3bfbc6  golean sha256 e0d47b48b83d9b0d…  go version go1.26.5 linux/amd64  nproc 32  load1 start 7.3 end 3.35  started 2026-09-18T18:49:38Z

empty probe (startup): median 0.0235 s over 7 runs [0.0216..0.0290], rss 71008 KB

steps per loop iteration (fuel bisection): alloc_new=85, append_cap=84, append_grow=84, heap_then_scalar=70, heap_then_scalar=49, map_write=44, read_fixed=55, scalar=49, struct_arr_100=47, write_fixed=51

**(e) scalar loop — per-step baseline** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `scalar(10000,)` | 0.1944 | 0.1798..0.1963 | 0.18 | 0.1709 | 17.09 |
| `scalar(20000,)` | 0.3561 | 0.3429..0.3615 | 0.34 | 0.3326 | 16.63 |
| `scalar(40000,)` | 0.6391 | 0.6290..0.6704 | 0.63 | 0.6156 | 15.39 |
| `scalar(80000,)` | 1.2459 | 1.2454..1.5292 | 1.23 | 1.2224 | 15.28 |

successive net ratios — 10000→20000: ×1.95 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 20000→40000: ×1.85 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 40000→80000: ×1.99 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

per machine step at n=80000: 312 ns (49 steps/iteration)

**(a) the review's loop: `append` growing from nil** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `append_grow(250,)` | 0.0353 | 0.0326..0.0366 | 0.02 | 0.0118 | 47.20 |
| `append_grow(500,)` | 0.0421 | 0.0417..0.0503 | 0.03 | 0.0186 | 37.20 |
| `append_grow(1000,)` | 0.0883 | 0.0837..0.0890 | 0.08 | 0.0648 | 64.80 |
| `append_grow(2000,)` | 0.1571 | 0.1460..0.1591 | 0.14 | 0.1336 | 66.80 |
| `append_grow(4000,)` | 0.4019 | 0.3927..0.4103 | 0.39 | 0.3784 | 94.60 |

successive net ratios — 250→500: ×1.58 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 500→1000: ×3.48 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1000→2000: ×2.06 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 2000→4000: ×2.83 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

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
| `write_fixed(10, 100)` | 0.0288 | 0.0261..0.0295 | 0.02 | 0.0053 | 53.00 |
| `write_fixed(100, 100)` | 0.0257 | 0.0238..0.0284 | 0.02 | 0.0022 | 22.00 |
| `write_fixed(1000, 100)` | 0.0260 | 0.0235..0.0292 | 0.02 | 0.0025 | 25.00 |
| `write_fixed(3000, 100)` | 0.0290 | 0.0268..0.0368 | 0.02 | 0.0055 | 55.00 |
| `write_fixed(10000, 100)` | 0.0344 | 0.0322..0.0349 | 0.02 | 0.0109 | 109.00 |

successive net ratios — 10→100: ×0.42 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 100→1000: ×1.14 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 1000→3000: ×2.20 (linear ×3.0, quadratic ×9.0, cubic ×27.0); 3000→10000: ×1.98 (linear ×3.3, quadratic ×11.1, cubic ×37.0)

**(b′) element writes at m = 10, write count varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `write_fixed(10, 100)` | 0.0288 | 0.0261..0.0295 | 0.02 | 0.0053 | 53.00 |
| `write_fixed(10, 1000)` | 0.0511 | 0.0504..0.0513 | 0.04 | 0.0276 | 27.60 |
| `write_fixed(10, 10000)` | 0.2671 | 0.2629..0.2675 | 0.25 | 0.2436 | 24.36 |

successive net ratios — 100→1000: ×5.21 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 1000→10000: ×8.83 (linear ×10.0, quadratic ×100.0, cubic ×1000.0)

**(i) 1,000 element reads `xs[0]`, slice length m varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `read_fixed(10, 1000)` | 0.0570 | 0.0555..0.0631 | 0.04 | 0.0335 | 33.50 |
| `read_fixed(100, 1000)` | 0.0569 | 0.0541..0.0583 | 0.04 | 0.0334 | 33.40 |
| `read_fixed(1000, 1000)` | 0.0546 | 0.0470..0.0559 | 0.04 | 0.0311 | 31.10 |
| `read_fixed(10000, 1000)` | 0.0543 | 0.0506..0.0567 | 0.04 | 0.0308 | 30.80 |

successive net ratios — 10→100: ×1.00 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 100→1000: ×0.93 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 1000→10000: ×0.99 (linear ×10.0, quadratic ×100.0, cubic ×1000.0)

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
| `alloc_new(1000,)` | 0.0787 | 0.0759..0.0796 | 0.07 | 0.0552 | 55.20 |
| `alloc_new(4000,)` | 0.3470 | 0.3392..0.4049 | 0.34 | 0.3235 | 80.87 |
| `alloc_new(16000,)` | 4.3211 | 4.2752..4.4230 | 4.31 | 4.2976 | 268.60 |
| `alloc_new(32000,)` | 16.6432 | 16.2222..16.9961 | 16.61 | 16.6197 | 519.37 |

successive net ratios — 1000→4000: ×5.86 (linear ×4.0, quadratic ×16.0, cubic ×64.0); 4000→16000: ×13.28 (linear ×4.0, quadratic ×16.0, cubic ×64.0); 16000→32000: ×3.87 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(d′) `make([]byte, 4)` per iteration (the 2026-09-03 audit probe)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `alloc_make4(1000,)` | (not run) | | | | |
| `alloc_make4(4000,)` | (not run) | | | | |
| `alloc_make4(16000,)` | (not run) | | | | |

**(h) live-heap size h vs a fixed 20,000-iteration scalar loop — allocation phase alone (w = 0)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_scalar(0, 0)` | 0.0241 | 0.0220..0.0251 | 0.01 | 0.0006 | — |
| `heap_then_scalar(1000, 0)` | 0.0597 | 0.0559..0.0604 | 0.05 | 0.0362 | 36.20 |
| `heap_then_scalar(10000, 0)` | 1.4744 | 1.4485..1.4796 | 1.46 | 1.4509 | 145.09 |
| `heap_then_scalar(40000, 0)` | 19.2896 | 18.6583..19.4227 | 19.28 | 19.2661 | 481.65 |

successive net ratios — 1000→10000: ×40.08 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 10000→40000: ×13.28 (linear ×4.0, quadratic ×16.0, cubic ×64.0)

**(h) … allocation phase + scalar phase (w = 20000)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_scalar(0, 20000)` | 0.3097 | 0.3073..0.3110 | 0.30 | 0.2862 | 14.31 |
| `heap_then_scalar(1000, 20000)` | 0.4560 | 0.4539..0.4723 | 0.45 | 0.4325 | 21.62 |
| `heap_then_scalar(10000, 20000)` | 3.1900 | 3.0555..3.2135 | 3.18 | 3.1665 | 158.33 |
| `heap_then_scalar(40000, 20000)` | 24.4634 | 24.3607..26.0351 | 24.45 | 24.4399 | 1222.00 |

scalar-phase cost at heap size h (= (h, 20000) net − (h, 0) net):
  h=0: 0.2856 s
  h=1000: 0.3963 s
  h=10000: 1.7156 s
  h=40000: 5.1738 s

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
