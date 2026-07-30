#import "@preview/euler-math:0.1.0": *
#import "../utils/utils.typ": *

= 整数和有理数

== 整数

#definition[整数][
  _整数_是形如$a bar.h b$的表达式，$a,b in NN$。两个整数$a bar.h b、c bar.h d$是相等的当且仅当$a +d = c+b$，令$ZZ$是所有整数构成的集合
]

#definition[整数的加法和乘法][

  两个整数的和定义为$(a bar.h b) + (c bar.h d) = (a+c) bar.h (b+d)$

  两个整数的积定义为$(a bar.h b) times (c bar.h d) = (a c + b d) bar.h (a d + b c)$
]

#lemma[整数加法和乘法是定义明确的][
  令$a,a',b,b',c,d in NN$，如果$(a bar.h b) = (a' bar.h b')$，那么有$(a bar.h b) + (c bar.h d) = (a' bar.h b')+ (c bar.h d)$，还有$(a bar.h b) times (c bar.h d) = (a' bar.h b') times (c bar.h d)$，还有$(c bar.h d) + (a bar.h b) = (c bar.h d) + (a' bar.h b')$，还有$(c bar.h d) times (a bar.h b) = (c bar.h d) times (a' bar.h b')$，因此整数加法和乘法是定义明确的运算.

  #proof[
    + $(a bar.h b) + (c bar.h d) = (a' bar.h b')+ (c bar.h d)$

      左式$=(a+c) bar.h (b+d) =$，右式$=(a'+c) bar.h (b'+d)$，所以欲证$ a+c+b'+d=b+d+a'+c $由于$(a bar.h b) = (a' bar.h b')$，那么$a+b'=a'+b$，两端同时加$c+d$，即可得到待证式子

    + $(a bar.h b) times (c bar.h d) = (a' bar.h b') times (c bar.h d)$

      左式$=(a c + b d) bar.h (a d + b c)$，右式$=(a' c + b' d) bar.h (b' c + a' d)$，所以欲证$ a c + b d + b'c + a'd = a'c + b'd + a d + b c $在$a+b'=a'+b$两端同时乘$(c + d)$，即可得到待证式子

    + $(c bar.h d) + (a bar.h b) = (c bar.h d) + (a' bar.h b')$

      左式$=(c+a) bar.h (d +b)$，右式$=(c+a') bar.h (d + b')$，所以欲证$ c+a+d+b' = c+a'+d+b $在$a+b'=a'+b$两端同时加$(c + d)$，即可得到待证式子

    + $(c bar.h d) times (a bar.h b) = (c bar.h d) times (a' bar.h b')$

      左式$=(c a + b d) bar.h (d a + c b)$，右式$=(c a' + d b') bar.h (c b' + d a')$，所以欲证$ c a + b d +c b' + d a' = c a' + d b' + d a + c b $在$a+b'=a'+b$两端同时乘$(c + d)$，即可得到待证式子
  ]
]

#lemma[
  自然数$n$可以和整数$n bar.h 0$等同起来
]

#definition[整数的负运算][
  $(a bar.h b)$是一个整数，定义其负数为$-(a bar.h b) = (b bar.h a)$。特别的，对于正自然数$n = n bar.h 0$，定义它的负数为$-n = 0 bar.h n$
]

#lemma[整数的三歧性][
  $x$是一个整数，下面三个命题中恰好有一个为真
  + $x$是$0$
  + $x$是正自然数$n$
  + $x$是正自然数的负数$-n$

  #proof[

    + 首先证明至少有一个命题成立。由定义$x = a bar.h b$，其中$a,b in NN$，由自然数的三歧性，$a > b, a<b,a=b$恰有一个为真，当$a > b$时，存在正自然数$n$，使得$a = b+n$，所以$a bar.h b = n bar.h 0 = n$，于是此时$x$是正自然数；$a = b$时，有$a bar.h b = 0 bar.h 0 = 0$，此时$x$为$0$；当$a < b$时，存在正自然数$n$，使得$b = a+n$，于是有$a bar.h b =-(b bar.h a) = -(n bar.h 0) = -n$，所以此时$x$是一个正自然数的负数。

    + 接下来证明最多有一个为真。（1）和（2）不可能同时为真，因为正自然数定义为不为$0$的自然数；如果（1）和（3）同时为真，那么存在一个正自然数的负数$-n = 0$，所以有$-(n bar.h 0) = (0 bar.h 0) => (0 bar.h n) = (0 bar.h 0) => n = 0$，矛盾；如果（2）和（3）同时为真，那么存在一个正自然数$n$使得$n = -n$，于是$n bar.h 0 = -(n bar.h 0) = (0 bar.h n) => n + n = 0 => n = 0$，矛盾；

    + 于是整数的三歧性得证
  ]
]

#note-block[
  如果$n$是一个正自然数，那么$-n$称为一个负整数
]

#theorem[整数的代数定律][
  $x,y,z in ZZ$，有以下成立
  + $x + y = y + x$
  + $(x+y)+z = x+(y+z)$
  + $x+0=0+x=x$
  + $x+(-x) = (-x)+x = 0$
  + $x y=y x$
  + $(x y)z = x(y z)$
  + $x 1 = 1 x = x$
  + $x(y+z) = x y +x z$
  + $(y+z)x = y x + z x$
]

#note-block[
  上述的9个等式断定全体整数是一个_交换环_
]

#definition[减法运算][
  $x,y in ZZ$，
  $x - y := x + (-y)$
]

#note-block[
  由减法运算的定义可以得到$a - b = a+(-b) = (a bar.h 0) + (0 bar.h b) = a bar.h b$

  所以形式减法“$bar.h$”可以被替换为熟悉的减法符号“$-$”了。但是本节的习题中还要暂时出现，至少要到证明了负运算的良定义后才能放心使用
]

#theorem[整数没有零因子][
  $a,b in ZZ$，且满足$a b = 0$，那么$a = 0 or b = 0 or a = b = 0$
]

#lemma[整数的消去律][
  如果$a,b,c in ZZ$，且满足$a c = b c and c != 0$，那么$a = b$
]

#definition[整数排序][

  $n,m in ZZ$，$n>=m$或$m <=n$当且仅当存在$a in NN$，使得$n = m+a$；$n > m$或$m < n$当且仅当$n >= m and n !=m$
]

#lemma[序的性质][
  令$a,b,c in ZZ$，有以下成立
  + $a > b$当且仅当$a - b$是正自然数
  + 如果$a>b$，那么$a+c > b+c$
  + 如果$a>b$，而且$c$是正的，那么$a c > b c$
  + 如果$a > b$，那么$-a < -b$
  + 如果$a >b and b>c$，那么$a > c$
  + 序的三歧性
]

#practice-separate()

#problem[证明整数上相等的定义是自反、对称、可传递的][]

#problem[证明整数上负运算的定义是明确的，即如果$(a bar.h b) = (a' bar.h b')$，那么$-(a bar.h b) = -(a' bar.h b')$][]

#problem[证明$(-1) times a = -a$对任意整数$a$成立][]

#problem[证明整数的代数定律][]

#problem[证明整数没有0因子][]

#problem[证明整数的消去律][]

#problem[证明序的性质][]

#problem[证明归纳法原理不能直接用于整数][]


== 有理数

== 绝对值和整数运算

== 有理数的间隙
