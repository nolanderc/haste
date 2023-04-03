package main

import (
    "fmt"
    "github.com/valyala/fasthttp"
    "aahframe.work"
    "github.com/gin-gonic/gin"
)

var (
	matchSize = [...]int{128, 512, 2048, 16384, 0}
	matchPool [len(matchSize)]int
)

func main() {
    fmt.Printf("hello")
}

var bar = func() {
    x := make(map[string]string)
    x = nil
    if x != nil {}
}

