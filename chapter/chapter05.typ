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

    此外，这里的$N$隐含了是自然数
  ]
]

#definition[柯西序列（Cauchy sequences）][

  有理数序列$(a_n)_(n=0)^infinity$被称作_柯西序列_，当且仅当$forall epsilon in QQ and epsilon > 0$，序列$(a_n)_(n=0)^infinity$都是$epsilon$-稳定的

  #note-block[
    更加“极限”的定义是：称$a_0, a_1, ...$是柯西序列，当且仅当$forall epsilon > 0, exists N >=0$，满足$d(a_j, a_k) <= epsilon, forall j , k >= N$
  ]
]
