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
    x := Parent{}
    x.Method()
}

type Parent struct {
    Inner
}

type Inner struct {}

func (c Inner) Method() {}
