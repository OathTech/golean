package main

func main() { println(nanOut() != nanOut(), 1/negz() < 0) }

func nanOut() float64 { z := 0.0; return z / z }
func negz() float64 { z := 0.0; return -z }
func infOut() float64 { z := 0.0; return 1 / z }
func pair() (float64, float32) { z := 0.0; var z32 float32; return -z, z32 / z32 }
