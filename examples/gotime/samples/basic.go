package main

import (
    "fmt"
    "go/ast"
    "go/build"
    "go/build/constraint"
    "go/constant"
    "go/doc"
    "go/importer"
)

func main() {
    fmt.Printf("hello")
}

func blah(a string, b, c int) {
    return map[string]func(){}
}

