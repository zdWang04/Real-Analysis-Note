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
  $epsilon > 0$，现在要找$N >= 1$使得任意$i,j >= N$都有$d(a_i , a_j) <= epsilon$成立，对于$a_i,a_j$的取值有$ 0<a_i<= 1/N\ 0<a_j<=1/N \ => d(a_i,a_j) <= 1/N $于是只需要找到满足$d(a_i,a_j) <= 1/N < epsilon$的$N$，就可以保证，当$i,j >=N$时，$d(a_i,a_j)$都严格小于$epsilon$，那么就有$N > 1/epsilon$，由于$N$的取值在正整数上，所以利用先前证明的向下取整函数就有$N = floor(1/epsilon) + 1$.综上，对于任意的正数$epsilon$，都可以找到正整数$N = floor(1/epsilon) + 1$，使得任意$i,j>=N$，都有$d(a_i,a_j) < epsilon$成立，也因此，该序列为柯西序列

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

    $(a_n)_(n=0)^infinity$是柯西序列，那么任意$epsilon > 0$，存在$N in NN$，使得任意$j,k >= N$，都有$d(a_j,a_k) <= epsilon$成立.

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

#definition[$epsilon$-接近的序列][
  $(a_n)_(n=0)^infinity$和$(b_n)_(n=0)^infinity$是两个序列，$epsilon in QQ and epsilon > 0$，序列$(a_n)_(n=0)^infinity$是_$epsilon$-接近_于序列$(b_n)_(n=0)^infinity$的，当且仅当$abs(a_i- b_i) <= epsilon,forall i in NN$
]

#definition[最终$epsilon$-接近的序列][
  $(a_n)_(n=0)^infinity$和$(b_n)_(n=0)^infinity$是两个序列，$epsilon in QQ and epsilon > 0$，序列$(a_n)_(n=0)^infinity$是_最终$epsilon$-接近_于序列$(b_n)_(n=0)^infinity$的，当且仅当存在$N in NN$，使得$abs(a_i- b_i) <= epsilon, forall i >= N$成立
]

#definition[等价序列][
  $(a_n)_(n=0)^infinity$和$(b_n)_(n=0)^infinity$两个序列是等价的，当且仅当对于任意$epsilon in QQ^+$，存在$N in NN$，使得$abs(a_i - b_i) <= epsilon, forall i >= N$
]
#pagebreak()
#note-block[
  对于一个序列内部，它的收敛行为我们使用了（最终）$epsilon$-稳定性和柯西序列进行描述

  对于两个序列之间，将上面的内容进行类比，就得到（最终）$epsilon$-接近性和等价序列
]

#example[$(a_n)_(n=0)^infinity$和$(b_n)_(n=0)^infinity$是两个序列，其中$a_n = 1 + 10^(-n), b_n = 1 - 10^(-n)$，那么他们是等价的][
  $forall epsilon > 0$，要找到$N in NN$，使得$abs(a_n - b_n) <= epsilon, forall n >= N$，那么就有$ abs(1+10^(-n) - 1 + 10^(-n)) = 2 times 10^(-n) <= epsilon $当$n >= N$时，$2 times 10^(-n) <= 2 times 10^(-N)$那么即求$ 2 times 10^(-N) <= epsilon $由于$10^N > N, N in NN$，那么就有$10^(-N)< 1/N$，所以$ 2 times 1/N <= epsilon\ => N >=2/epsilon $所以对于任意正有理数$epsilon$，取$N = ceil(2/ epsilon)$即可
]

#practice-separate()

#problem[证明：如果$(a_n)_(n=1)^infinity$和$(b_n)_(n=1)^infinity$是等价的有理数序列，那么$(a_n)_(n=1)^infinity$是柯西序列，当且仅当$(b_n)_(n=1)^infinity$是柯西序列][

  #proof[
    由于两个序列是等价序列，那么$forall epsilon in QQ^+, exists N in NN$，使得$abs(a_n - b_n) <= epsilon/3, forall n >= N$

    - $=>$

      当$(a_n)_(n=1)^infinity$是柯西序列时，$forall epsilon in QQ^+, exists N' in NN$，使得$abs(a_j - a_k) <= epsilon/3, forall j, k >= N'$

      那么当$N'' = max(N, N')$时，就有$ abs(b_j - b_k) <= abs(b_j - a_j) + abs(a_j - a_k) + abs(a_k - b_k) <=epsilon/3 + epsilon/3 + epsilon/3 = epsilon, forall j, k >= N'' $于是$(b_n)_(n=1)^infinity$是柯西序列

    - $arrow.l.double$同理
  ]

  #note-block[
    证明关键是利用$epsilon/3$凑配出$abs(b_j - b_k) <= epsilon$的不等式
  ]
]

#problem[证明：如果$(a_n)_(n=1)^infinity$和$(b_n)_(n=1)^infinity$是等价的有理数序列，那么$(a_n)_(n=1)^infinity$是有界的，当且仅当$(b_n)_(n=1)^infinity$是有界的][

  #proof[
    两序列为等价序列，那么$forall epsilon in QQ^+, exists N in NN$，使得$abs(a_j - b_j) <= epsilon, forall j >= N$

    - $=>$

      由于$(a_n)_(n=1)^infinity$是有界的，那么$exists M in QQ^+$，使得$abs(a_i) <= M, forall i in NN^+$，于是$ abs(b_i) <= abs(b_i - a_i) + abs(a_i) <= epsilon + M $于是$(b_n)_(n=1)^infinity$是有界的

    - $arrow.l.double$同理
  ]
]

== 实数的构造

#definition[实数][
  + _实数_被定义为形如$"LIM"_(n -> infinity) a_n$的对象，其中$(a_n)_(n=1)^infinity$是_有理数柯西序列_
  + 两个实数$"LIM"_(n -> infinity) a_n$和$"LIM"_(n -> infinity) b_n$称作是_相等的_，当且仅当$(a_n)_(n=1)^infinity$和$(b_n)_(n=1)^infinity$是_等价的柯西序列_
  + 所有实数组成的集合记作$RR$

  #note-block[
    这里的$"LIM"$和先前构造整数时的形式减法$bar.h$以及构造有理数时的形式除法$slash.double$一样，当对实数的代数性质以及运算进行了足够的证明之后，$"LIM"$会和早已熟悉的$lim$匹配
  ]
]

#theorem[实数相等是良定义的][
  令$x = "LIM"_(n -> infinity) a_n,y = "LIM"_(n -> infinity) b_n,z= "LIM"_(n -> infinity) c_n, x,y,z in RR$
  #proof[
    + $x = x$

      $a_n(n=1)^infinity$和$a_n(n=1)^infinity$是等价的柯西序列，所以就有$x = x$

    + $x = y => y = x$

      $x = y =>$，$a_n(n=1)^infinity$和$b_n(n=1)^infinity$是等价的柯西序列，于是$b_n(n=1)^infinity$和$a_n(n=1)^infinity$是等价的柯西序列，于是$y = x$

    + $x = y and y = z => x = z$

      $x = y => forall epsilon/2 in QQ^+, exists N_1 in NN$，使得$abs(a_i - b_i) <= epsilon/2, i>= N_1$成立

      $y = z => forall epsilon/2 in QQ^+, exists N_2 in NN$，使得$abs(b_i - c_i) <= epsilon/2, i>= N_2$成立

      所以有$ abs(a_i - c_i) <= abs(a_i - b_i) + abs(b_i - c_i) <= epsilon/2 + epsilon/2 = epsilon, i>= max(N_1, N_2) $成立，所以$(a_n)_(n=1)^infinity$和$(c_n)_(n=1)^infinity$是等价的柯西序列，所以$x = z$

    + 综上证明了实数相等的自反、对称和传递性质，实数的相等是良定义的
  ]
]
#definition[实数加法][
  $x = "LIM"_(n -> infinity) a_n, y = "LIM"_(n -> infinity) b_n$是实数，那么$x + y := "LIM"_(n -> infinity) (a_n + b_n)$
]

#lemma[柯西序列的和也是柯西的][

  $x = "LIM"_(n -> infinity) a_n, y = "LIM"_(n -> infinity) b_n, x,y in RR => x + y in RR$（即证明$(a_n+b_n)_(n=1)^infinity$也是柯西序列）

  #proof[
    由实数定义，有$ forall epsilon/2 in QQ^+,exists N_1 in NN^+,abs(a_j - a_k) <= epsilon/2, forall j,k >= N_1\ forall epsilon/2 in QQ^+, exists N_2 in NN^+, abs(b_j - b_k) <= epsilon/2, forall j,k >= N_2 $根据实数加法定义$x + y = "LIM"_(n -> infinity)(a_n + b_n)$，于是有$ abs(a_i + b_i - a_k -b_k) <= abs(a_j - a_k)+ abs(b_j - b_k) <= epsilon/2 + epsilon/2 = epsilon, forall j,k>= max(N_1, N_2) $所以$(a_n + b_n)_(n=1)^infinity$是柯西序列，综上，柯西序列的和也是柯西的
  ]
]

#lemma[等价的柯西序列的和也是等价的][
  $x = "LIM"_(n -> infinity) a_n, y = "LIM"_(n -> infinity) b_n,x' = "LIM"_(n -> infinity) a'_n, y' = "LIM"_(n -> infinity) b'_n, x, x', y in RR and x = x' => x+y = x' + y$

  #proof[

    由于$x = x'$，那么$forall epsilon in QQ^+, exists N in NN^+,abs(a_i - a'_i) <= epsilon, forall i >= N$于是就有$ abs(a_i +b_i - a'_i - b_i) <= epsilon, forall i >= N $于是柯西序列$(a_n+b_n)_(n=1)^infinity$和$(a'_n + b_n)_(n=1)^infinity$是等价的，所以$x = x' => x + y = x' + y$

  ]
  #note-block[
    这一部分就是证明实数加法是良定义的，完整的证明应当是$x = x' and y = y' => x+y = x'+y'$，在证明时使用$epsilon/2$不难得到
  ]
]

#definition[实数的乘法][

  $x = "LIM"_(n->infinity)a_n, y = "LIM"_(n->infinity)b_n$，$x,y$都是实数，定义$x y:="LIM"_(n->infinity)a_n b_n$
]

#lemma[实数乘法是良定义的][
  $x = "LIM"_(n->infinity)a_n, y = "LIM"_(n->infinity)b_n,x'="LIM"_(n->infinity)a'_n, x,x',y in RR$，那么$x y = x'y$

  #proof[

    由于$(b_n)_(n=1)^infinity$是柯西序列，那么它是有界的，令界为$M$，由于$x = x'$，那么$ exists N in NN^+, abs(a_j - a'_j) <= epsilon/M, epsilon in QQ^+,j>= N $所以有$ abs(a_j b_j - a'_j b_j) = abs(a_j - a'_j) abs(b_j) <= epsilon/M M = epsilon, j>= N $于是序列$(a_n)_(n=1)^infinity (b_n)_(n=1)^infinity$和$(a'_n)_(n=1)^infinity (b_n)_(n=1)^infinity$是等价的，所以$x y = x'y$
  ]
  #note-block[
    同实数加法是良定义的证明，还应当证明$y = y' => x y = x y'$
  ]
]

#note-block[
  一个有理数可以看作是一个各个项相等的柯西序列，比如$x in QQ, x = "LIM"_(n->infinity) x$，其中是序列是$x,x,x,...,x,...$，正因如此，可以将有理数“嵌入”到实数中去，证明细节见问题 5.34的证明
]

#definition[实数的相反数][

  $-x := (-1) times x$

  #note-block[
    令$x = "LIM"_(n->infinity)a_n$根据实数相反数的定义和乘法就有$ -x = -1 times x = "LIM"_(n->infinity)-1 times "LIM"_(n->infinity)a_n = "LIM"_(n->infinity)-a_n $
  ]
]

#definition[实数的减法][

  $x - y := x + (-y)$
  #note-block[
    令$x = "LIM"_(n->infinity)a_n, y = "LIM"_(n->infinity)b_n$，类似的，根据实数相反数的定义和乘法和加法就有$ x - y = x + (-y) = "LIM"_(n->infinity)a_n + "LIM"_(n->infinity)-b_n = "LIM"_(n->infinity)(a_n - b_n) $
  ]
]

#note-block[
  现在有了实数的加法、乘法和减法，可以证明实数也满足整数的代数定律
]

#definition[远离0的序列][
  一个有理数序列$(a_n)_(n=1)^infinity$是远离$0$的，当且仅当$exists c > 0$，满足$abs(a_i) >= c, forall i >= 1$
]

#lemma[$x in RR and x != 0$，那么存在远离$0$的柯西序列$(a_n)_(n=1)^infinity$，满足$x = "LIM"_(n->infinity)a_n$][
  #proof[
    由于$x in RR$，那么不妨令$x = "LIM"_(n->infinity)b_n$，那么序列$(b_n)_(n=1)^infinity$是柯西序列，因此有$ forall epsilon/2 in QQ^+, exists N in NN^+, abs(b_n - b_m) <= epsilon/2, forall n,m >= N $此外，由于$x != 0$，那么序列$(b_n)_(n=0)^infinity$与序列${0,...,0,...}$不等价，于是存在$n_0 >=N$，使得$abs(b_(n_0)) = abs(b_(n_0) - 0) > epsilon$.结合之前的结果就有$                               abs(b_(n_0) - b_n) & <= epsilon/2, n>=N \
                                        abs(b_(n_0)) & > epsilon \
    => abs(b_n) >= abs(b_(n_0)) - abs(b_(n_0) - b_n) & >= epsilon/2, n>= N $
    接下来定义一个新的序列$(a_n)_(n=0)^infinity$，它满足$ a_n = cases(epsilon/2 \, &n<N, b_n\, &n>=N) $

    容易验证序列$(a_n)_(n=0)^infinity$是远离$0$的，接下来证明它与序列$(b_n)_(n=0)^infinity$是等价的.$ abs(a_i - b_i) = cases(abs(epsilon/2 - b_i)&\, i<N, 0&\, i>=N) $所以对于任意正有理数$epsilon$，存在正整数$N$，当$i >=N$时，$abs(a_i - b_i) = 0 < epsilon$，于是$(a_n)_(n=1)^infinity$和$(b_n)_(n=1)^infinity$是等价的
  ]
  #note-block[
    这个结果说明，每个非零实数总与某个远离0的柯西序列对应
  ]
]

#lemma[如果一个柯西序列$(a_n)_(n=1)^infinity$是远离$0$的，那么序列$(a_n^(-1))_(n=1)^infinity$也是柯西序列][
  由于$(a_n)_(n=1)^infinity$是远离$0$的，那么$ exists c >0, abs(a_i)>= c, forall i in NN^+ $由于$(a_n)_(n=1)^infinity$是柯西序列，那么$ forall c^2 epsilon >0, exists N in NN^+, abs(a_j - a_k) <= c^2 epsilon, j,k >= N $接下来考察序列$(a_n^(-1))_(n=1)^infinity$，有$ abs(a^(-1)_j - a^(-1)_m) = abs((a_j-a_k)/(a_j a_k)) <= abs(a_j - a_k)/c^2 <= (c^2 epsilon)/c^2 = epsilon, forall j,k>= N $于是序列$(a_n^(-1))_(n=1)^infinity$也是柯西序列
]

#note-block[
  + 引理 5.27 保证了一个柯西序列是远离0的，那么它的形式极限就能和一个非0的实数对应
  + 引理 5.28 保证了远离0的柯西序列的“倒数序列”也是柯西的，也即“倒数序列”的形式极限也是实数中的一个元素，保证了倒数运算对非0实数的封闭性

  有了以上两个引理的打底，可以对倒数运算进行定义了
]

#definition[实数的倒数][
  $x$是一个非零实数，$(a_n)_(n=1)^infinity$是一个远离$0$的柯西序列，且满足$x = "LIM"_(n->infinity)a_n$.

  定义$x$的倒数为$ x^(-1) := "LIM"_(n->infinity)a_n^(-1) $
]

#lemma[实数的倒数是良定义的][
  $(a_n)_(n=1)^infinity$和$(b_n)_(n=1)^infinity$是远离$0$的柯西序列且$"LIM"_(n->infinity)a_n = "LIM"_(n->infinity)b_n$，那么$"LIM"_(n->infinity)a_n^(-1) = "LIM"_(n->infinity)b_n^(-1)$

  #proof[

    令$P$是一个实数，定义为
    $ P := ("LIM"_(n->infinity)a_n^(-1)) times ("LIM"_(N->infinity)a_n) times ("LIM"_(n->infinity)b_n^(-1)) $
    利用实数乘法就有
    $ P= "LIM"_(n->infinity)a_n^(-1) a_n b_n^(-1) = "LIM"_(n->infinity)b_n^(-1) $
    由于$"LIM"_(n->infinity)a_n = "LIM"_(n->infinity)b_n$，也有$ P = ("LIM"_(n->infinity)a_n^(-1)) times ("LIM"_(n->infinity)b_n) times ("LIM"_(n->infinity)b_n^(-1)) $根据实数乘法$ P = "LIM"_(n->infinity)a_n^(-1) b_n b_n^(-1) = "LIM"_(n->infinity)a_n^(-1) $所以就有$ "LIM"_(n->infinity)a_n^(-1) = "LIM"_(n->infinity)b_n^(-1) $因此，实数的倒数运算是良定义的
  ]
]

#definition[实数的除法][
  $x, y in RR and y != 0$，定义实数的除法为$ x/y := x y^(-1) $
]


#note-block[
  在证明实数的加法、乘法、负运算和倒数运算的良定义后，也可以证明实数满足有理数的代数定律
]

#practice-separate()

#problem[证明形式极限是良定义的][见定理 5.18的证明]
#problem[证明实数乘法是良定义的][见引理 5.23的证明]
#problem[$a,b in QQ$，证明$a = b <=> "LIM"_(n->infinity)a = "LIM"_(n->infinity)b$][
  #proof[
    + $=>$

      $a = b => a-b = 0 => abs(a-b) = 0$

      于是$forall epsilon in QQ^+, abs(a -b) = 0 < epsilon$，所以序列$a,...,a,...$和序列$b,...,b,...$等价，于是$"LIM"_(n->infinity)a = "LIM"_(n->infinity)b$

    + $arrow.double.l$

      由于$"LIM"_(n->infinity)a = "LIM"_(n->infinity)b$，那么$ forall epsilon in QQ^+, exists N in NN^+, abs(a - b) <= epsilon $取$epsilon = abs(a-b)/2$，就有$ abs(a-b) <= abs(a-b)/2 => abs(a-b)/2 <= 0 $由于绝对值的非负性，所以$abs(a-b)/2 = 0 => a = b$
  ]
]

#problem[$(a_n)_(n=0)^infinity$是有界有理数序列，令$(b_n)_(n=0)^infinity$是$(a_n)_(n=0)^infinity$的等价序列，证明$(b_n)_(n=0)^infinity$也是有界的][

  由于$(a_n)_(n=0)^infinity$是有界序列，那么$ abs(a_i) <= M, i in NN,M in QQ^+ $
  由于$(b_n)_(n=0)^infinity$是$(a_n)_(n=0)^infinity$的等价序列，那么$ forall epsilon in QQ^+, exists N in NN, abs(b_i - a_i) <= epsilon, i >= N $
  于是就有$ abs(b_i) <= abs(b_i - a_i) + abs(b_i) <= epsilon + M, i >= N $对于${b_i:i<N}$的部分，是一个有限序列，先前证明过引理：有限序列也是有界的，不妨令界为$W$，于是$abs(b_i) <= max(W, M+epsilon), forall i in NN$，于是序列$(b_n)_(n=0)^infinity$也是有界的
]

== 实数的序
