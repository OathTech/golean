commit 68b261e60d2f6107b1948b5a2a67607e3b5a8fbd  golean sha256 231df9a99f459d4a…  go version go1.26.5 linux/amd64  nproc 32  load1 start 1.52 end 1.34  started 2026-09-18T06:35:44Z

empty probe (startup): median 0.0190 s over 7 runs [0.0178..0.0194], rss 72936 KB

steps per loop iteration (fuel bisection): alloc_new=85, append_cap=84, append_grow=84, heap_then_scalar=70, heap_then_scalar=49, map_write=44, read_fixed=55, scalar=49, struct_arr_100=47, write_fixed=51

**(e) scalar loop — per-step baseline** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `scalar(10000,)` | 0.1432 | 0.1372..0.1438 | 0.13 | 0.1242 | 12.42 |
| `scalar(20000,)` | 0.2530 | 0.2510..0.2686 | 0.25 | 0.2340 | 11.70 |
| `scalar(40000,)` | 0.5409 | 0.5160..0.5561 | 0.53 | 0.5219 | 13.05 |
| `scalar(80000,)` | 0.9832 | 0.9451..1.0287 | 0.97 | 0.9642 | 12.05 |

successive net ratios — 10000→20000: ×1.88 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 20000→40000: ×2.23 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 40000→80000: ×1.85 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

per machine step at n=80000: 246 ns (49 steps/iteration)

**(a) the review's loop: `append` growing from nil** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `append_grow(250,)` | 0.0417 | 0.0404..0.0431 | 0.03 | 0.0227 | 90.80 |
| `append_grow(500,)` | 0.1318 | 0.1315..0.1337 | 0.12 | 0.1128 | 225.60 |
| `append_grow(1000,)` | 0.7193 | 0.7020..0.7230 | 0.71 | 0.7003 | 700.30 |
| `append_grow(2000,)` | 4.5785 | 4.2615..4.5799 | 4.57 | 4.5595 | 2279.75 |
| `append_grow(4000,)` | 30.4374 | 30.3735..30.5752 | 30.42 | 30.4184 | 7604.60 |

successive net ratios — 250→500: ×4.97 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 500→1000: ×6.21 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1000→2000: ×6.51 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 2000→4000: ×6.67 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(f) in-place `append`, w = c (no spill)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `append_cap(250, 250)` | 0.0542 | 0.0507..0.0542 | 0.04 | 0.0352 | 140.80 |
| `append_cap(500, 500)` | 0.1966 | 0.1963..0.2043 | 0.19 | 0.1776 | 355.20 |
| `append_cap(1000, 1000)` | 1.2573 | 1.2566..1.2606 | 1.25 | 1.2383 | 1238.30 |
| `append_cap(2000, 2000)` | 9.1112 | 9.0766..9.1209 | 9.10 | 9.0922 | 4546.10 |

successive net ratios — 250→500: ×5.05 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 500→1000: ×6.97 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1000→2000: ×7.34 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(f′) 100 in-place appends, capacity c varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `append_cap(100, 100)` | 0.0257 | 0.0250..0.0260 | 0.02 | 0.0067 | 67.00 |
| `append_cap(200, 100)` | 0.0297 | 0.0295..0.0300 | 0.02 | 0.0107 | 107.00 |
| `append_cap(400, 100)` | 0.0448 | 0.0442..0.0465 | 0.04 | 0.0258 | 258.00 |
| `append_cap(800, 100)` | 0.0965 | 0.0955..0.1102 | 0.09 | 0.0775 | 775.00 |
| `append_cap(1600, 100)` | 0.3121 | 0.3108..0.3223 | 0.30 | 0.2931 | 2931.00 |
| `append_cap(3200, 100)` | 1.1334 | 1.1213..1.1346 | 1.13 | 1.1144 | 11144.00 |
| `append_cap(6400, 100)` | 4.4627 | 4.4294..4.4735 | 4.45 | 4.4437 | 44437.00 |

successive net ratios — 100→200: ×1.60 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 200→400: ×2.41 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 400→800: ×3.00 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 800→1600: ×3.78 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1600→3200: ×3.80 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 3200→6400: ×3.99 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(b) 100 element writes `xs[0] = v`, slice length m varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `write_fixed(10, 100)` | 0.0211 | 0.0206..0.0216 | 0.01 | 0.0021 | 21.00 |
| `write_fixed(100, 100)` | 0.0234 | 0.0230..0.0242 | 0.01 | 0.0044 | 44.00 |
| `write_fixed(1000, 100)` | 0.1438 | 0.1333..0.1440 | 0.13 | 0.1248 | 1248.00 |
| `write_fixed(3000, 100)` | 0.9750 | 0.9750..0.9752 | 0.97 | 0.9560 | 9560.00 |
| `write_fixed(10000, 100)` | 10.7162 | 10.6953..10.8854 | 10.71 | 10.6972 | 106972.00 |

successive net ratios — 10→100: ×2.10 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 100→1000: ×28.36 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 1000→3000: ×7.66 (linear ×3.0, quadratic ×9.0, cubic ×27.0); 3000→10000: ×11.19 (linear ×3.3, quadratic ×11.1, cubic ×37.0)

**(b′) element writes at m = 10, write count varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `write_fixed(10, 100)` | 0.0211 | 0.0206..0.0216 | 0.01 | 0.0021 | 21.00 |
| `write_fixed(10, 1000)` | 0.0346 | 0.0337..0.0352 | 0.03 | 0.0156 | 15.60 |
| `write_fixed(10, 10000)` | 0.1629 | 0.1614..0.1681 | 0.15 | 0.1439 | 14.39 |

successive net ratios — 100→1000: ×7.43 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 1000→10000: ×9.22 (linear ×10.0, quadratic ×100.0, cubic ×1000.0)

**(i) 1,000 element reads `xs[0]`, slice length m varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `read_fixed(10, 1000)` | 0.0340 | 0.0337..0.0346 | 0.03 | 0.0150 | 15.00 |
| `read_fixed(100, 1000)` | 0.0348 | 0.0345..0.0351 | 0.03 | 0.0158 | 15.80 |
| `read_fixed(1000, 1000)` | 0.0340 | 0.0335..0.0345 | 0.02 | 0.0150 | 15.00 |
| `read_fixed(10000, 1000)` | 0.0368 | 0.0364..0.0371 | 0.03 | 0.0178 | 17.80 |

successive net ratios — 10→100: ×1.05 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 100→1000: ×0.95 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 1000→10000: ×1.19 (linear ×10.0, quadratic ×100.0, cubic ×1000.0)

**(c) aggregate shape — 100 writes each** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| struct{y,x int}: s.x = i | 0.0209 | 0.0204..0.0219 | 0.01 | 0.0019 | 19.00 |
| struct{a [100]byte; x int}: s.x = i | 0.0241 | 0.0241..0.0245 | 0.01 | 0.0051 | 51.00 |
| struct{a [1000]byte; x int}: s.x = i | 0.1346 | 0.1344..0.1387 | 0.12 | 0.1156 | 1156.00 |
| struct{a [10000]byte; x int}: s.x = i | 10.9320 | 10.9277..10.9381 | 10.92 | 10.9130 | 109130.00 |
| struct{a []byte; x int}, len(a)=100: s.x = i | 0.0209 | 0.0206..0.0212 | 0.01 | 0.0019 | 19.00 |
| struct{a []byte; x int}, len(a)=10000: s.x = i | 0.0222 | 0.0218..0.0233 | 0.01 | 0.0032 | 32.00 |
| [10000]byte: b[0] = v | 10.8162 | 10.7102..10.8616 | 10.80 | 10.7972 | 107972.00 |
| [10][1000]byte: a[0][0] = v | 1.1621 | 1.1233..1.2161 | 1.15 | 1.1431 | 11431.00 |
| [100][100]byte: a[0][0] = v | 0.2638 | 0.2488..0.2684 | 0.25 | 0.2448 | 2448.00 |
| [][]byte 10×1000 (separate cells): xs[0][0] = v | 0.1443 | 0.1432..0.1443 | 0.13 | 0.1253 | 1253.00 |

**(d) allocation-only loops** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `alloc_new(1000,)` | 0.0582 | 0.0538..0.0594 | 0.05 | 0.0392 | 39.20 |
| `alloc_new(4000,)` | 0.2644 | 0.2637..0.2753 | 0.26 | 0.2454 | 61.35 |
| `alloc_new(16000,)` | 3.5967 | 3.5847..3.6192 | 3.58 | 3.5777 | 223.61 |
| `alloc_new(32000,)` | 13.7896 | 13.6326..13.9243 | 13.78 | 13.7706 | 430.33 |

successive net ratios — 1000→4000: ×6.26 (linear ×4.0, quadratic ×16.0, cubic ×64.0); 4000→16000: ×14.58 (linear ×4.0, quadratic ×16.0, cubic ×64.0); 16000→32000: ×3.85 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(d′) `make([]byte, 4)` per iteration (the 2026-09-03 audit probe)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `alloc_make4(1000,)` | 0.0513 | 0.0497..0.0550 | 0.04 | 0.0323 | 32.30 |
| `alloc_make4(4000,)` | 0.2715 | 0.2598..0.2784 | 0.26 | 0.2525 | 63.12 |
| `alloc_make4(16000,)` | 3.6383 | 3.6301..3.6436 | 3.63 | 3.6193 | 226.21 |

successive net ratios — 1000→4000: ×7.82 (linear ×4.0, quadratic ×16.0, cubic ×64.0); 4000→16000: ×14.33 (linear ×4.0, quadratic ×16.0, cubic ×64.0)

**(h) live-heap size h vs a fixed 20,000-iteration scalar loop — allocation phase alone (w = 0)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_scalar(0, 0)` | 0.0198 | 0.0193..0.0204 | 0.01 | 0.0008 | — |
| `heap_then_scalar(1000, 0)` | 0.0460 | 0.0458..0.0467 | 0.04 | 0.0270 | 27.00 |
| `heap_then_scalar(10000, 0)` | 1.1943 | 1.1915..1.2314 | 1.18 | 1.1753 | 117.53 |
| `heap_then_scalar(40000, 0)` | 18.4168 | 17.9410..18.5490 | 18.40 | 18.3978 | 459.94 |

successive net ratios — 1000→10000: ×43.53 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 10000→40000: ×15.65 (linear ×4.0, quadratic ×16.0, cubic ×64.0)

**(h) … allocation phase + scalar phase (w = 20000)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_scalar(0, 20000)` | 0.2570 | 0.2561..0.2746 | 0.25 | 0.2380 | 11.90 |
| `heap_then_scalar(1000, 20000)` | 0.3988 | 0.3964..0.4282 | 0.39 | 0.3798 | 18.99 |
| `heap_then_scalar(10000, 20000)` | 2.9995 | 2.9965..3.0081 | 2.99 | 2.9805 | 149.02 |
| `heap_then_scalar(40000, 20000)` | 24.7915 | 23.7481..24.8738 | 24.78 | 24.7725 | 1238.63 |

scalar-phase cost at heap size h (= (h, 20000) net − (h, 0) net):
  h=0: 0.2372 s
  h=1000: 0.3528 s
  h=10000: 1.8052 s
  h=40000: 6.3747 s

**(h′) live-heap size h vs 300 in-place appends — allocation phase alone (w = 0)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_append(0, 0)` | 0.0188 | 0.0185..0.0200 | 0.01 | -0.0002 | — |
| `heap_then_append(10000, 0)` | 1.1827 | 1.1819..1.1879 | 1.17 | 1.1637 | 116.37 |
| `heap_then_append(40000, 0)` | 18.0058 | 17.8399..18.4945 | 17.99 | 17.9868 | 449.67 |

**(h′) … + 300 in-place appends (w = 300)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_append(0, 300)` | 0.0723 | 0.0719..0.0743 | 0.06 | 0.0533 | 177.67 |
| `heap_then_append(10000, 300)` | 1.3512 | 1.3473..1.3555 | 1.34 | 1.3322 | 4440.67 |
| `heap_then_append(40000, 300)` | 18.7576 | 18.7466..18.8871 | 18.74 | 18.7386 | 62462.00 |

append-phase cost at heap size h (= (h, 300) net − (h, 0) net):
  h=0: 0.0535 s
  h=10000: 0.1685 s
  h=40000: 0.7518 s

**(g) map writes, n distinct int keys** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `map_write(500,)` | 0.0282 | 0.0280..0.0283 | 0.02 | 0.0092 | 18.40 |
| `map_write(1000,)` | 0.0416 | 0.0416..0.0419 | 0.03 | 0.0226 | 22.60 |
| `map_write(2000,)` | 0.0806 | 0.0781..0.0850 | 0.07 | 0.0616 | 30.80 |
| `map_write(4000,)` | 0.1993 | 0.1980..0.2070 | 0.19 | 0.1803 | 45.08 |

successive net ratios — 500→1000: ×2.46 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1000→2000: ×2.73 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 2000→4000: ×2.93 (linear ×2.0, quadratic ×4.0, cubic ×8.0)
