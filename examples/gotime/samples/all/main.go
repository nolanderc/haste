package main

import (
    "fmt"
    "github.com/valyala/fasthttp"
    "aahframe.work"
    "github.com/gin-gonic/gin"
    "text/template"
)

type A struct {}
type B A

func main() {
    const N = 3
    var index [N]int
}

type FuncMap map[string]interface{}

// Funcs adds the elements of the argument map to the template's function map.
// It must be called before the template is parsed.
// It panics if a value in the map is not a function with appropriate return
// type. However, it is legal to overwrite elements of the map. The return
// value is the template, so calls can be chained.
func Funcs(funcMap FuncMap) {
    x := template.FuncMap(funcMap)
}
