package main

import (
    "fmt"
    "github.com/valyala/fasthttp"
    "aahframe.work"
    "github.com/gin-gonic/gin"
)

func main() {
    fmt.Printf("hello")
}

var bar = func() {
	const stackBufSize = 128
	buf := make([]byte, 0, stackBufSize)
}

