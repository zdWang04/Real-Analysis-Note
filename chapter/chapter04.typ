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

#problem[证明整数上相等的定义是自反、对称、可传递的][
  #proof[
    令$x, y, z in ZZ$，分别为$x = (a bar.h b), y=(c bar.h d), z=(e bar.h f)$

    + $x = x <=> x = x$

      $x = x => (a bar.h b) = (a bar.h b) => a+b = a+b$，由自然数相等的自反性可得证，反向亦然

    + $x = y <=> y = z$

      $x = y => a+d=c+b => c + b = a+d => (c bar.h d) = (a bar.h b) => y = z$，反向同理

    + $x = y and y = z => x = z$

      $(a bar.h b) = (c bar.h d) => a + d=b+c$，$(c bar.h d) = (e bar.h f) => c + f = e + d$，将两式相加有$a+c+d+f = b + c + e +d$，由消去律有$a+f=b+e$，于是就有$(a bar.h b) = (e bar.h f)$，即$x = z$
  ]
]

#problem[证明整数上负运算的定义是明确的，即如果$(a bar.h b) = (a' bar.h b')$，那么$-(a bar.h b) = -(a' bar.h b')$][
  #proof[
    $
      & (a bar.h b) = (a' bar.h b') \
      & => a + b' = a' + b \
      & => b' + a = b + a' \
      & => (b' bar.h a') = (b bar.h a) \
      & => -(a bar.h b) = -(a' bar.h b')
    $
  ]
]
#note-block[可以用减号了！]

#problem[证明$(-1) times a = -a$对任意整数$a$成立][
  #proof[$forall a in ZZ$，令$a = (x - y), x in NN, y in NN$

    $
      & (-1) times a = (0 - 1) times (x - y) \
      & = ((0x +1y) - (0y + x)) \
      & = (y - x) \
      & = -a
    $]
]

#problem[证明整数的代数定律][
  #proof[$x,y,z in ZZ$，令$x = (a - b), y = (c - d), z= (e - f)$

    + $x + y = y + x$
      $
        x+y = ((a+c) - (b+d)) = ((c+a) - (d+b)) = y+x
      $

    + $(x+y)+z = x+(y+z)$
      $
        (x+y)+z = ((a+c) - (b+d)) + (e - f) = ((a+c+e) - (b+d+f))\
        x+(y+z) = (a - b) + ((c+e) -(d+f)) = ((a+c+e) - (b + d+f))\
        (x+y)+z = x+(y+z)
      $

    + $x+0=0+x=x$

      $ x+0 = (a - b) + (0 - 0) = ((a+0) - (b+0)) = (a - b) = x $由先前的加法交换律，就有$x + 0 = 0 + x = x$

    + $x + (-x) = (-x) + x = 0$

      $ (a - b) + (b - a) = ((a+b) - (b+a)) = (0 - 0) = 0 $由先前的加法交换律，就有$x + (-x) = (-x) + x = 0$

    + $x y = y x$
      $
        (a - b) times (c - d) & = ((a c + b d) - (b c + a d)) \
                              & = ((c a + d b) - (c b + d a)) \
                              & = (c - d) times (a - b)
      $
    + $(x y)z = x(y z)$
      $ & "  "((a - b) times (c - d)) times (e - f) \
      & = ((a c + b d) - (b c + a d)) times (e - f) \
      & = (a c e + b d e + b c f + a d f) - (a c f + b d f + b c e + a d e) \
      & "  "(a - b) times ((c - d)) times (e - f) \
      & = (a - b) times ((c e + d f) - (d e + c f)) \
      & = (a c e + a d f + b d e + b c f) - (a d e + a c f + b c e + b d f) $于是$(x y)z = x(y z)$

    + $x 1 = 1 x = x$
      $ (a - b) times (1 times 0) = (a 1 + b 0) - (a 0 + b 1) = a - b = x $由先前的乘法交换律，就有$1 x = x 1 = x$

    + $x(y+z) = x y +x z$
      $
        & (a - b)((c - d) + (e - f)) \
        & = (a - b)((c+e) - (d +f)) \
        & = (a c + a e + b d + b f) - (a d + a f + b c + b e) \
        & = ((a c + b d) - (a d + b c)) + ((a e + b f) - (a f + b e)) \
        & = x y + x z
      $

    + $(y + z)x = y x + z x$
      由先前的乘法交换律和分配律证明
  ]
]

#problem[证明整数没有0因子][
  #proof[
    令$x,y in ZZ$，如果$x y = 0$，对$x$进行分类讨论
    + $x = 0$，那么有$x y =0$成立
    + $x$是正自然数$a$，那么$a y = 0$，就有$y = 0$
    + $x$是正自然数$a$的负数$-a$，那么$-a y = 0$，于是$a y = -0 = 0$，所以$y = 0$
    + 由整数的三歧性，已经考虑了所有情况，且都可以得到$x = 0 or y = 0$，从而得证
  ]
]

#problem[证明整数乘法的消去律][
  #proof[
    $ a c = b c \
    a c - b c = 0 \
    (a - b)c = 0 $由于整数没有零因子，那么$a - b = 0 or c = 0$，由于$c != 0$，那么$a - b=0$，于是有$a = b$]
]

#problem[证明序的性质][
  #proof[
    $a,b,c in ZZ$
    + 由于$a > b$，那么$exists x in N$，使得$a = b + x$，并且$b != a$，于是有$a - b = x$且$a - b != 0$，所以$a > b$，则有$a - b$是正自然数；如果$a - b = x$且$x$是正自然数，那么$a = b +x$，于是有$a >= b$，由于$x$是正自然数，那么$a - b != 0 => a!=b$，所以$a - b$是正自然数，则有$a > b$
    + 如果$a > b$，那么存在正自然数$x$使得$a = b + x$，于是$a + c = b + x + c = b + c + x$，就有$a + c > b + c$
    + 如果$a > b$，那么存在正自然数$x$使得$a = b + x$，于是$a c = (b + x)c = b c + x c$，由于$c$是正的，那么$x c > 0$，于是$a c > b c$
    + 如果$a > b$，那么存在正自然数$x$使得$a = b + x$，所以$-a = -b + (-x) => -a + x = -b$，所以$a > b => -b > -a$
    + 如果$a > b and b > c$，那么存在正自然数$x,y$分别满足$a = b + x$和$b = c + y$，于是有$a = c + (y + x)$，$(y + x)$也是正自然数，所以$a > c$
    + 序的三歧性
      - 至少有一个成立，令整数$a = x - y, x in ZZ, y in ZZ$，$n$为正自然数，由整数的三歧性有
      $  x - y = 0 & => x = y \
       x - y = n & => x = y + n => x >y \
      x - y = -n & =>y = x + n => x < y $于是至少有一个成立
      - 至多有一个成立，如果$a = b$，那么无法找到正自然数$x,y$使得$a = b + x$或$b = a + y$成立，于是此时$a > b$和$a < b$都不成立；如果$a > b$，那么存在正自然数$x$使得$a = b + x$，那么$a != b$，且无法找到正自然数$y$使得$b = a + y$；同理，如果$a < b$成立，其他两个命题不成立
  ]
]

#problem[证明归纳法原理不能直接用于整数，构造一个具体的例子][
  #proof[
    $n in ZZ$，令命题$P(n) = n >= 0$，当$n = 0$时，$P(n) = 0$成立，现在归纳的假设$P(n)$成立，那么$P(n+1) = n+1 > n >=0$，所以$P(n)$对于$n in ZZ$成立。取$n = -1$，那么$P(-1) = -1 >= 0$不成立
  ]

  #note-block[
    整数之所以不能用归纳法，是因为无法选定归纳起点，无法从$ZZ$中选出最小的整数
  ]
]

== 有理数

#definition[有理数][
  有理数是形如$a slash.double b$的表达式，其中$a, b in ZZ and b !=0$，$a slash.double b = c slash.double d <=> a d = b c$，所有有理数的集合记作$QQ$
]

#definition[有理数的运算][$a slash.double b, c slash.double d in QQ$

  和定义为$(a slash.double b) +(c slash.double d) = (a d + b c) slash.double (b d)$

  乘积定义为$(a slash.double b) * (c slash.double d) = (a b) slash.double (c d)$

  负运算定义为$-(a slash.double b) = (-a) slash.double b$
]

#note-block[
  有理数$a slash.double 1$与整数$a$有相同的性质：
  $ (a slash.double 1) + (b slash.double 1) & = (a + b) slash.double 1 \
  (a slash.double 1) * (b slash.double 1) & = (a b) slash.double (1) \
                      -(a slash.double 1) & = (-a) slash.double 1 $并且$ a slash.double 1 = b slash.double 1 <=> a = b $
  因此可以认为
  $a slash.double 1 eq.triple a, forall a in ZZ$
]

#lemma[有理数的和、乘积和负运算是定义明确的]

#lemma[有理数$a slash.double b = 0 <=> a = 0 and b!= 0$
][
  #proof[根据有理数的定义$b != 0$，如果$a slash.double b = 0 = 0 slash.double$；那么$a 1 =a = b 0 = 0$，如果$a = 0$，那么$a 1 = b 0$，于是有$a slash.double b = 0 slash.double 1 = 0$]
]

#definition[倒数运算][
  $x in QQ and x != 0$并且$x = a slash.double b$，定义其倒数为$x^(-1) = b slash.double a$
]

#theorem[有理数的代数定律][
  $x,y,z in QQ$，有以下成立
  + $x + y = y + z$
  + $(x+y)+z = x+(y+z)$
  + $x + 0 = 0 + x = x$
  + $x + (-x) = (-x) + x = 0$
  + $x y = y x$
  + $(x y)z = x(y z)$
  + $x 1 = 1 x = x$
  + $x(y + z) = x y + x z$
  + $(y + z)x = y x + z x$
  如果$x != 0$，那么有
  + $x x^(-1) =x^(-1) x= 1$
]

#note-block[
  以上的等式断定了有理数集$QQ$构成了域
]

#definition[商的定义][
  定义$x, y in ZZ$的商$x slash z$为$ x slash y := x y^(-1) $
]

#note-block[
  $x slash y = x y^(-1) = (x slash.double 1) (1 slash.double y) = x slash.double y$

  上面的推理对每一个整数$x$和每一个非零整数$y$成立，于是现在可以将“$slash.double$”替代为“$slash$”了
]

#definition[正负有理数][
  $x, y in QQ$，$a,b in ZZ$

  有理数$x = a slash b$是正的$<=>$ $a > 0 and b >0$

  有理数$x = a slash b$是负的$<=>$ $x = -y$，其中$y$是正的有理数
]

#lemma[有理数的三歧性][
  $x in QQ$，那么下面只有一个命题是成立的
  + $x = 0$
  + $x$是正的
  + $x$是负的
]

#definition[有理数的序][
  $x,y in QQ$

  $x > y <=> x-y$是正的

  $x < y <=> x-y$是负的

  当$x > y or x = y$时，$x >= y$

  当$x < y or x = y$时，$x <= y$
]

#theorem[有理数的序的基本性质][
  $x,y,z in QQ$，下列成立
  + 有理数的序的三歧性
  + $x < y <=> y > x$
  + $x < y and y < z => x < z$
  + $x < y => x + z < y + z$
  + $x < y and z$是正的$=> x z < y z$
]

#practice-separate()

#problem[有理数相等是自反、对称和可传递的][]

#problem[有理数的和、积和负运算是良定义的][]

#problem[证明有理数的代数运算][]

#problem[证明有理数的三歧性][]

#problem[证明有理数的序的基本性质][]

#problem[$x,y,z in QQ, x<y$，$z$是负的，那么$x z > y z$][]


== 绝对值和整数运算

== 有理数的间隙
