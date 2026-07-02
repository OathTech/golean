package main

type duplicateMethodReceiver struct{}

func (duplicateMethodReceiver) m() {}

func (duplicateMethodReceiver) m() {}
