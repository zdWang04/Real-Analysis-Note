#import "@preview/theorion:0.6.0": *
#import cosmos.fancy: *
#import "utils/utils.typ": note-cover
#show: show-theorion


#set heading(numbering: "1.1")

#show regex("\\p{Han}+"): it => text(font: "LXGW WenKai Mono", it)
#set text(lang: "zh")

// #set par(first-line-indent: 1em, justify: true) // 自然段空格
// #set page(height: auto) // 不分页

#set-qed-symbol[#math.qed]
#show math.equation.where(block: true): eq => block(
  width: 100%,
  align(center, eq),
)

#note-cover(
  title: "实分析笔记",
  subtitle: "Note to《Analysis I & II》by Terence Tao",
  author: "zdWang04",
  // date: [2026年9月17日],
)

#outline(title: "目录")
#pagebreak()

#include "contents/chapters/chapter01.typ"
#include "contents/chapters/chapter02.typ"
#include "contents/chapters/chapter03.typ"
#include "contents/chapters/chapter04.typ"
#include "contents/chapters/chapter05.typ"
#include "contents/chapters/chapter06.typ"

#include "contents/appendix/appendixA.typ"
#include "contents/appendix/appendixB.typ"
