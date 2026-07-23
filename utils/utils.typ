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
    radius: 4pt
  )[
    #text(weight: "bold", size: 1.2em, fill: rgb("3a4d63"))[#title]
  ]
  #v(8pt)                   
  #content                  
]