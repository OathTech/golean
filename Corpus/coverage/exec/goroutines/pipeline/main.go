package main

// Confluent pipelines: single sender per channel keeps every value
// stream FIFO-pinned (spec: "Channels act as first-in-first-out
// queues"), so the aggregate is schedule-independent.

func pipelineTwoStage() int {
	gen := make(chan int)
	doubled := make(chan int)
	go func() {
		for i := 1; i <= 4; i++ {
			gen <- i
		}
		close(gen)
	}()
	go func() {
		for v := range gen {
			doubled <- v * 2
		}
		close(doubled)
	}()
	sum := 0
	for v := range doubled {
		sum = sum*10 + v
	}
	return sum
}

func pipelineBufferedStage() int {
	gen := make(chan int, 2)
	out := make(chan int)
	go func() {
		for i := 5; i <= 9; i++ {
			gen <- i
		}
		close(gen)
	}()
	go func() {
		total := 0
		for v := range gen {
			total += v
		}
		out <- total
	}()
	return <-out
}

// Values flow both directions through one worker: main sends work,
// worker replies on its own channel, per-item lockstep.
func pipelineRequestReply() int {
	req := make(chan int)
	rep := make(chan int)
	go func() {
		for v := range req {
			rep <- v * v
		}
		close(rep)
	}()
	acc := 0
	for i := 1; i <= 3; i++ {
		req <- i
		acc = acc*100 + <-rep
	}
	close(req)
	return acc
}

func main() {
	pipelineTwoStage()
	pipelineBufferedStage()
	pipelineRequestReply()
}
