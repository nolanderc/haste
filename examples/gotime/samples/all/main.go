package main

import (
    "fmt"
    "github.com/valyala/fasthttp"
    "aahframe.work"
    "github.com/gin-gonic/gin"
    "gorm.io/gorm"
    "github.com/beego/beego/v2"
    "github.com/beego/beego/v2/server/web"
)

func main() {
    const N = 3
    var index [N]int

    var containers Containers
    containers.filter()
}

type Containers []int

func (c Containers) filter() {}

