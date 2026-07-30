#let note-block(content, title: "侧记") = block(
  fill: rgb("f5f5f5"),
  inset: 12pt,
  radius: 6pt,
  width: 100%,
  stroke: none,
)[
  // 低饱和度的淡蓝灰色标签背景
  #box(
    fill: rgb("e5ecf4"),
    inset: (x: 8pt, y: 4pt),
    radius: 4pt,
  )[
    #text(weight: "bold", size: 1.2em, fill: rgb("3a4d63"))[#title]
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
