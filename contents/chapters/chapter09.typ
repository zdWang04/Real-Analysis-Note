#import "@preview/theorion:0.6.0": *
#import cosmos.fancy: *

= 实数上的连续函数

== 实数轴上的子集

#definition[区间][
    $a, b in RR^*$，定义闭区间$[a, b]$为
    $
        [a, b] := {x in RR^*: a<= x <= b}
    $

    定义半开区间为
    $
        (a, b] := {x in RR^*: a < x <= b}\
        [a, b) := {x in RR^*: a <= x < b}\
    $

    定义开区间为
    $
        (a, b) := {x in RR^*: a < x < b}
    $

    此外，称$a$为这些区间的左端点，$b$为这些区间的右端点
]

#definition[$epsilon$-黏附点][
    $X subset.eq RR, epsilon in RR^+, x in RR$，称$x$是$epsilon$-黏附于集合$X$的，当且仅当$exists y in X$，满足$abs(x - y) <= epsilon$
]

#definition[黏附点][
    $X subset.eq RR, x in RR$，称$x$是$X$的黏附点，当且仅当
    $
        forall epsilon in RR^+, exists y in X, abs(x - y) <= epsilon
    $
]

#tip-block[
    再一次的，$epsilon$-黏附点这个非正式的概念只会在早期学习中使用，当有了足够好的工具后，这个概念会被舍弃
]

#definition[闭包(Closure)][
    $X subset.eq RR$，$X$的闭包定义为集合
    $
        overline(X) := {x in RR: forall epsilon in RR^+, exists y in X, abs(x - y) <= epsilon}
    $也就是所有$X$的黏附点组成的集合
]

#lemma[闭包的基本性质][
    $X, Y subset.eq RR$，有如下成立
    + $X subset.eq overline(X)$
    + $overline(X union Y) = overline(X) union overline(Y)$
    + $overline(X inter Y) subset.eq overline(X) inter overline(Y)$
    + $X subset.eq Y => overline(X) subset.eq overline(Y)$
]
#proof[
    + 任选$x in X$，存在元素$x in X$，使得$abs(x - x) = 0$，小于任意正实数，所以$x in overline(X)$，于是$X subset.eq overline(X)$
    + asd
]

















#pagebreak()
