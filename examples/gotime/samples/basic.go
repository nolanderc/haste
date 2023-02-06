package main

import "fmt"

func main() {
    123
}

type Reader interface {
	Read(p []byte) (n int, err error)
	Close() error
}

var x, y float32 = -1, -2
var (
	i       int
	u, v, s = 2.0, 3.0, "bar"
)
