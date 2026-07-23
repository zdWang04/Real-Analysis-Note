#import "@preview/euler-math:0.1.0": *

// 1. COVER PAGE AND CONFIGURATION
#show: euler-math.with(
  title: [实分析I笔记],
  subtitle: [],
  author: [dongdong],
)
// Choose the language
#set text(lang: "zh")

// 2. TABLE OF CONTENTS
#outline(title: "目录", indent: auto)
#pagebreak()

// 3. SECTIONS AND THEORETICAL CONTENT

#include "chapter/chapter1.typ"
#pagebreak()
#include "chapter/chapter2.typ"
#pagebreak()
#include "chapter/chapter3.typ"
#pagebreak()


