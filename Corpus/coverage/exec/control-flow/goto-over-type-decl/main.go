package main

func gotoOverTypeDecl() int {
	goto done
	type localInt int
done:
	var x localInt = 1
	return int(x)
}
