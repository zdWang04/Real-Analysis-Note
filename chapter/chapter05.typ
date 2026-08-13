#import "@preview/euler-math:0.1.0": *
#import "../utils/utils.typ": *

= 实数

== 柯西序列

#definition[序列][
  $m in ZZ$，_有理数序列_是一个函数，记作$(a_n)_(n=m)^infinity: {n in ZZ : n>=m}-> QQ$，比如$(a_n)_(n=m)^infinity$是一组有理数$a_m,a_(m+1),a_(m+2),...$
]

#definition[$epsilon$-稳定性][
  $epsilon > 0$，序列$(a_n)_(n=0)^infinity$是$epsilon$-稳定的，当且仅当$forall j,k in NN$，都有$d(a_j,a_k) <= epsilon$

  #note-block[
    注意这里序列的角标是从$0$开始的，意味这有理数序列是函数$(a_n)_(n=0)^infinity : NN -> QQ$，所以在之后表示序列中任意两项都是$epsilon$-接近的时候，角标$j , k$都在自然数中选取
  ]
]

// #example[$epsilon$-稳定性][
//   + 有理数序列$(10^(-n-1))_(n=0)^infinity$是$0.1$-稳定的，但不是$0.01$-稳定的，比如$d(10^(-1), 10^(-2)) = 0.09 > 0.01$
// ]

#definition[最终$epsilon$-稳定性][
  $epsilon > 0$，称序列$(a_n)_(n=0)^infinity$是最终$epsilon$-稳定的，当且仅当存在一个$N >= 0$，使得$forall j,k >= N, d(a_j, d_k) <= epsilon$

  #note-block[
    已经能够一点点的看出标准的极限定义的样子了，这里引入$N$的动机，就是_避免序列早期的波动_影响我们对极限收敛的判断，倘若一个序列前10项完全不能做到$epsilon$-稳定，但是从11项起都能做到$epsilon$-稳定，就可以认为他是_最终$epsilon$-稳定性_的，因为极限过程的长期行为下，该序列收敛

    // 此外，这里的$N$隐含了是自然数
  ]
]

#definition[柯西序列（Cauchy sequences）][

  有理数序列$(a_n)_(n=0)^infinity$被称作_柯西序列_，当且仅当$forall epsilon in QQ and epsilon > 0$，序列$(a_n)_(n=0)^infinity$都是$epsilon$-稳定的

  #note-block[
    更加“极限”的定义是：称$a_0, a_1, ...$是柯西序列，当且仅当$forall epsilon > 0, exists N >=0$，满足$d(a_j, a_k) <= epsilon, forall j , k >= N$
  ]
]

#example[$a_n := 1/n$的序列$a_1, a_2,...$是柯西序列][
  $epsilon > 0$，现在要找$N >= 1$使得任意$i,j >= N$都有$d(a_i , a_j) <= epsilon$成立，对于$a_i,a_j$的取值有$ 0<a_i<= 1/N\ 0<a_j<=1/N \ => d(a_i,a_j) <= 1/N $于是只需要找到满足$d(a_i,a_j) <= 1/N < epsilon$的$N$，就可以保证，当$i,j >=N$时，$d(a_i,a_j)$都严格小于$epsilon$，那么就有$N > 1/epsilon$，由于$N$的取值在正整数上，所以利用先前证明的向下取整函数就有$N = floor(1/epsilon) + 1$。综上，对于任意的正数$epsilon$，都可以找到正整数$N = floor(1/epsilon) + 1$，使得任意$i,j>=N$，都有$d(a_i,a_j) < epsilon$成立，也因此，该序列为柯西序列

  #note-block[
    柯西序列的定义中是要求$d(x_i,x_j) <= epsilon$，实际上严格小于也可以，因为这比小于等于更强
  ]
]

#definition[有界序列][
  $M >= 0$是有理数
  + 有限序列$a_1,a_2,...,a_n$以$M$为界，当且仅当$abs(a_i) <= M, forall 1<=i<=n$

  + 无限序列$(a_n)_(n=1)^infinity$以$M$为界，当且仅当$abs(a_i) <= M, forall i >= 1$

  + 称一个序列是有界的，当且仅当存在一个正有理数$M$，使得该序列以$M$为界
]

#example[无限序列$((-1)^(n-1) n)_(n=1)^infinity$不是有界的][
  倘若以$M in QQ and M >= 0$为界，那么令$x = floor(M)$，易知$x$是正整数，于是$a_(x+1) = a(floor(M) + 1)$，$abs(a_(x+1)) = floor(M) + 1 > M$，矛盾，所以是无界的
]

#lemma[有限序列是有界的][
  序列$a_1, a_2, ..., a_n$是有界的

  #proof[
    对$n$进行归纳，当$n = 1$时，序列为$a_1$，对于任意的有理数$M >= abs(a_1)$，$M$都是该序列的界；现在归纳性的假设$a_1,...,a_n$为有界序列，且界为$M, M >= 0$，现在证明$n+1$的情况，对于序列$a_1,a_2,...a_n,a_(n+1)$，易知界为$M+abs(a_(n+1))$，现在进行验证$ & forall 1<=i<=n, abs(a_i) <= M <= M + abs(a_(n+1)) \
    & i = n+1, "  "abs(a_(n+1)) <=M + abs(a_(n+1)) $于是序列$a_1,...,a_(n+1)$也是有界的，归纳结束
  ]
]

#lemma[柯西序列是有界的][
  #proof[

    $(a_n)_(n=0)^infinity$是柯西序列，那么任意$epsilon > 0$，存在$N in NN$，使得任意$j,k >= N$，都有$d(a_j,a_k) <= epsilon$成立。

    那么对于一个给定的$epsilon$，可以将该柯西序列分为$a_1,...,a_(N-1)$和$a_N,...$两个序列

    + 前者为有限序列，由先前证明的引理，必然有界，不妨令界为$M$

    + 后者是一个无限序列，且满足$d(a_j,a_k) <= epsilon, forall j,k >= N$，取$k = N$，就有$ & d(a_j, a_N) <= epsilon \
      & => abs(a_j - a_N) <= epsilon \
      & =>abs(a_j) <= abs(a_j - a_N) + abs(a_N) <= epsilon + abs(a_N) \ $上述的$j >= N$且是任取的，那么对于后者无限序列是有界的，界为$epsilon + abs(a_N)$

    + 综上，柯西序列是有界的，界为$max(M, epsilon + abs(a_N))$
  ]
]

#practice-separate()

#problem[柯西序列是有界的][
  见上的证明过程，主要是分段考虑
]

== 等价的柯西序列
