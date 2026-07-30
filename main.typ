#import "@preview/euler-math:0.1.0": *

#show regex("\\p{Han}+"): it => text(font: "LXGW WenKai Mono", it)
#show: euler-math.with(
  title: [实分析I笔记],
  subtitle: [],
  author: [dongdong],
)
// #show math.equation.where(block: true): set align(left) // 左对齐行间公式

#set text(lang: "zh")

#outline(title: "目录", indent: auto)
#pagebreak()


#include "chapter/chapter01.typ"
#pagebreak()
#include "chapter/chapter02.typ"
#pagebreak()
#include "chapter/chapter03.typ"
#pagebreak()


