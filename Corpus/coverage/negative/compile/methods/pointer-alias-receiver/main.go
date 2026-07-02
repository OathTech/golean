package main

type receiverBase struct{}

type receiverPointerAlias *receiverBase

func (receiverPointerAlias) m() {}
