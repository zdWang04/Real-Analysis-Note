// #let note-block(content, title: "侧记") = block(
//   fill: rgb("f5f5f5"),
//   inset: 12pt,
//   radius: 6pt,
//   width: 100%,
//   stroke: none,
// )[
//   // 低饱和度的淡蓝灰色标签背景
//   #box(
//     fill: rgb("e5ecf4"),
//     inset: (x: 8pt, y: 4pt),
//     radius: 4pt,
//   )[
//     #text(weight: "bold", size: 1.2em, fill: rgb("3a4d63"))[#title]
//   ]
//   #v(8pt)
//   #content
// ]
#let note-block(content, title: "侧记") = block(
  fill: rgb("f5f5f5"), // 保留您最喜欢的淡灰色背景
  width: 100%,
  stroke: (left: 4pt + rgb("888888")), // 左侧加粗装饰边框（使用了沉稳的深灰色）
  inset: (left: 12pt, right: 12pt, top: 10pt, bottom: 10pt), // 调整内边距，让文字离左边线有优雅的距离
)[
  // 标题：侧记（保留了比底色稍深的灰色精致小标签样式）
  #box(
    fill: rgb("e8e8e8"),
    inset: (x: 8pt, y: 4pt),
    radius: 3pt,
  )[
    #text(weight: "bold", size: 0.95em, fill: rgb("444444"))[#title]
  ]
  #v(8pt)
  #content
]

#let practice-separate() = block(
  width: 100%,
  breakable: false,
  above: 3em,
  below: 2.5em,
  fill: rgb("eff3f0"),
  radius: 8pt,
  inset: (top: 16pt, bottom: 16pt),
)[
  #align(center)[
    #text(
      size: 2em,
      weight: "bold",
      tracking: 0.6em,
      fill: rgb("3d4f41"),
    )[练习]
  ]
]
