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

      由于$(a_n)_(n=1)^infinity$是有界的，那么$exists M in QQ^+$，使得$abs(a_i) <= M, forall i in ZZ^+$，于是$ abs(b_i) <= abs(b_i - a_i) + abs(a_i) <= epsilon + M $于是$(b_n)_(n=1)^infinity$是有界的

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
    由实数定义，有$ forall epsilon/2 in QQ^+,exists N_1 in ZZ^+,abs(a_j - a_k) <= epsilon/2, forall j,k >= N_1\ forall epsilon/2 in QQ^+, exists N_2 in ZZ^+, abs(b_j - b_k) <= epsilon/2, forall j,k >= N_2 $根据实数加法定义$x + y = "LIM"_(n -> infinity)(a_n + b_n)$，于是有$ abs(a_i + b_i - a_k -b_k) <= abs(a_j - a_k)+ abs(b_j - b_k) <= epsilon/2 + epsilon/2 = epsilon, forall j,k>= max(N_1, N_2) $所以$(a_n + b_n)_(n=1)^infinity$是柯西序列，综上，柯西序列的和也是柯西的
  ]
]

#lemma[等价的柯西序列的和也是等价的][
  $x = "LIM"_(n -> infinity) a_n, y = "LIM"_(n -> infinity) b_n,x' = "LIM"_(n -> infinity) a'_n, y' = "LIM"_(n -> infinity) b'_n, x, x', y in RR and x = x' => x+y = x' + y$

  #proof[

    由于$x = x'$，那么$forall epsilon in QQ^+, exists N in ZZ^+,abs(a_i - a'_i) <= epsilon, forall i >= N$于是就有$ abs(a_i +b_i - a'_i - b_i) <= epsilon, forall i >= N $于是柯西序列$(a_n+b_n)_(n=1)^infinity$和$(a'_n + b_n)_(n=1)^infinity$是等价的，所以$x = x' => x + y = x' + y$

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

    由于$(b_n)_(n=1)^infinity$是柯西序列，那么它是有界的，令界为$M$，由于$x = x'$，那么$ exists N in ZZ^+, abs(a_j - a'_j) <= epsilon/M, epsilon in QQ^+,j>= N $所以有$ abs(a_j b_j - a'_j b_j) = abs(a_j - a'_j) abs(b_j) <= epsilon/M M = epsilon, j>= N $于是序列$(a_n)_(n=1)^infinity (b_n)_(n=1)^infinity$和$(a'_n)_(n=1)^infinity (b_n)_(n=1)^infinity$是等价的，所以$x y = x'y$
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
    由于$x in RR$，那么不妨令$x = "LIM"_(n->infinity)b_n$，那么序列$(b_n)_(n=1)^infinity$是柯西序列，因此有$ forall epsilon/2 in QQ^+, exists N in ZZ^+, abs(b_n - b_m) <= epsilon/2, forall n,m >= N $此外，由于$x != 0$，那么序列$(b_n)_(n=0)^infinity$与序列${0,...,0,...}$不等价，于是存在$n_0 >=N$，使得$abs(b_(n_0)) = abs(b_(n_0) - 0) > epsilon$.结合之前的结果就有$                               abs(b_(n_0) - b_n) & <= epsilon/2, n>=N \
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
  由于$(a_n)_(n=1)^infinity$是远离$0$的，那么$ exists c >0, abs(a_i)>= c, forall i in ZZ^+ $由于$(a_n)_(n=1)^infinity$是柯西序列，那么$ forall c^2 epsilon >0, exists N in ZZ^+, abs(a_j - a_k) <= c^2 epsilon, j,k >= N $接下来考察序列$(a_n^(-1))_(n=1)^infinity$，有$ abs(a^(-1)_j - a^(-1)_m) = abs((a_j-a_k)/(a_j a_k)) <= abs(a_j - a_k)/c^2 <= (c^2 epsilon)/c^2 = epsilon, forall j,k>= N $于是序列$(a_n^(-1))_(n=1)^infinity$也是柯西序列
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

      由于$"LIM"_(n->infinity)a = "LIM"_(n->infinity)b$，那么$ forall epsilon in QQ^+, exists N in ZZ^+, abs(a - b) <= epsilon $取$epsilon = abs(a-b)/2$，就有$ abs(a-b) <= abs(a-b)/2 => abs(a-b)/2 <= 0 $由于绝对值的非负性，所以$abs(a-b)/2 = 0 => a = b$
  ]
]

#problem[$(a_n)_(n=0)^infinity$是有界有理数序列，令$(b_n)_(n=0)^infinity$是$(a_n)_(n=0)^infinity$的等价序列，证明$(b_n)_(n=0)^infinity$也是有界的][

  由于$(a_n)_(n=0)^infinity$是有界序列，那么$ abs(a_i) <= M, i in NN,M in QQ^+ $
  由于$(b_n)_(n=0)^infinity$是$(a_n)_(n=0)^infinity$的等价序列，那么$ forall epsilon in QQ^+, exists N in NN, abs(b_i - a_i) <= epsilon, i >= N $
  于是就有$ abs(b_i) <= abs(b_i - a_i) + abs(b_i) <= epsilon + M, i >= N $对于${b_i:i<N}$的部分，是一个有限序列，先前证明过引理：有限序列也是有界的，不妨令界为$W$，于是$abs(b_i) <= max(W, M+epsilon), forall i in NN$，于是序列$(b_n)_(n=0)^infinity$也是有界的
]

#problem[证明$"LIM"_(n->infinity)1/n = 0$][
  即证明序列$(1/n)_(n=1)^infinity$与序列$(0)_(n=1)^infinity$是等价的$ 1/n >= epsilon => 0< n <= 1/epsilon $取$N = ceil(1/epsilon)$，于是$ forall epsilon in QQ^+, exists N in ZZ^+,forall j >= N, abs(1/j - 0) = abs(1/j) <= epsilon $于是二序列等价，于是$"LIM"_(n->infinity)1/n = 0$
]

== 实数的序

#definition[正/负远离$0$的序列][

  $(a_n)_(n=1)^infinity$是一个有理数序列
  1. 该序列是正远离$0$的$<=> exists c in QQ^+, forall i in ZZ^+, a_i >= c$
  2. 该序列是负远离$0$的$<=> exists -c in QQ^-, forall i in ZZ^+, a_i <= -c$
]

#definition[实数的正负][
  + 实数$x$是正的$<=> x = "LIM"_(n->infinity)a_n and a_n$是正远离$0$的
  + 实数$x$是负的$<=> x = "LIM"_(n->infinity)a_n and a_n$是负远离$0$的

  #note-block[
    注意实数被定义为了柯西序列的形式极限，所以想要对实数的正负下定义，先要对序列的正负下定义，定义5.36正是这个目的
  ]
]

#theorem[实数的三歧性][
  实数$x = "LIM"_(n->infinity)a_n$是正的、负的、$0$，这三种情况同时只有一个成立
  #proof[
    + 首先证明至少有一个成立，也即证明三种同时不成立是不可能的

      如果$x$是正的，那么$exists c in QQ^+, forall i in ZZ^+, a_i >= c$

      如果$x$是负的，那么$exists -c in QQ^-, forall i in ZZ^+, a_i <= -c$

      如果$x$是$0$，那么$forall epsilon in QQ^+, exists N in ZZ^+, abs(a_i - 0) = abs(a_i) <= epsilon, forall i >=N$

      假设上述三个都不成立，由于$(a_n)_(n=0)^infinity$是柯西序列，那么$ abs(a_n - a_m) <= epsilon/2, n,m>=N $由于不是0，那么$ abs(a_i) > epsilon, exists i >= N $取$n_0>=N$，就有$ abs(a_(n_0)) > epsilon => a_(n_0) > epsilon or a_(n_0) < -epsilon $

      - 当$a_(n_0) > epsilon$时，任意$m>=N$都有$ abs(a_m - a_(n_0)) <= epsilon/2 => a_m > -epsilon/2 + a_(n_0) > -epsilon/2 + epsilon = epsilon/2 >0 $这与不是正的矛盾
      - 当$a_(n_0) < -epsilon$时，任意$m >=N$都有$ a_m < epsilon/2 + a_(n_0) < epsilon/2 -epsilon = -epsilon/2 < 0 $这与不是负的矛盾

      综上，至少有一个成立

    + 现在证明至多有一个成立
      - 如果$x$是正的，那么$exists c in QQ^+, forall i in ZZ^+, a_i >= c$，显然$forall i in ZZ^+, a_i >= c > -c$，所以$x$不会是负的，同时$abs(a_i - 0) = abs(a_i) >= c$，所以对于任意的$epsilon in QQ^+$，无法找到$N in ZZ^+$，使得$abs(a_i - 0) = abs(a_i) <= epsilon, i>=N$，所以$(a_n)_(n=1)^infinity$与柯西序列$0,0,...$不等价，所以$x$也不是0
      - 如果$x$是负的，那么$exists -c in QQ^-,forall i in ZZ^+, a_i <= -c$，显然$forall i in ZZ^+, a_i <= -c <=c$，所以$x$不是正的，同时$abs(a_i - 0) = abs(a_i) >= c$，同理，$(a_n)_(n=1)^infinity$不与柯西序列$0,0,...$等价，所以$x$也不是0
      - 如果$x=0$，那么$(a_n)_(n=1)^infinity$与柯西序列$0,0,...$等价，于是$ forall epsilon in QQ^+, exists N in ZZ^+, forall i>=N, abs(a_i - 0)=abs(a_i) <= epsilon $于是$ -epsilon<=a_i<=epsilon, i >= N $那么无法找到$c in QQ^+$，使得$a_i >= c, forall i in ZZ^+$，因为$a_i>=-epsilon$无法得到$a_i>=c$，所以$x$不是正的，同理$x$也不是负的
  ]
]

#lemma[实数$x$是负的，当且仅当$-x$是正的][
  #proof[
    由于$x in RR$，那么令$x = "LIM"_(n->infinity)a_n$
    + $=>$

      由于$x$是负的，那么$(a_n)_(n=1)^infinity$是负远离$0$的，所以$ exists -c in QQ^-, forall i in ZZ^+, a_i <= -c $根据实数的相反数运算，就有$-x = "LIM"_(n->infinity)(-a_n)$，所以就有$ forall i in ZZ^+, -a_i >= c $其中$c in QQ^+$，这正是柯西序列正远离$0$的定义，于是$-x$是正的

    + $arrow.double.l$

      由于$-x$是正的，那么$(-a_n)_(n=1)^infinity$是正远离$0$的，那么$ exists c in QQ^+, forall i in ZZ^+, -a_i >=c $根据实数的相反数运算，就有$x = "LIM"_(n->infinity)a_n = "LIM"_(n->infinity)(-(-a_n))$，于是$ forall i in ZZ^+, a_i = -(-a_i) <= -c $其中$-c in QQ^-$，这正是柯西序列负远离$0$的定义，于是$x$是负的
  ]
]

#lemma[实数$x,y$都是正的，那么$x+y$和$x y$也是正的][
  令$x = "LIM"_(n->infinity)a_n$，$y = "LIM"_(n->infinity)b_n$

  #proof[

    - 由于$x,y$都是正的，那么$ & exists c_1 in QQ^+, forall i in ZZ^+, a_i >= c_1 \
      & exists c_2 in QQ^+, forall i in ZZ^+, b_i >= c_2 $由于$x + y = "LIM"_(n->infinity)(a_n+b_n)$，所以有$ forall i in ZZ^+, a_i + b_i >= c_1 + c_2 $其中$c_1+c_2 in QQ^+$，于是$(a_n+b_n)_(n=1)^infinity$是正远离$0$的，所以$x+y$是正的

    - 其他同前，由于$x y = "LIM"_(n->infinity)(a_n b_n)$，那么$ forall i in ZZ^+, a_i b_i >= c_1 c_2 $其中$c_1 c_2 in QQ^+$，于是序列$(a_n b_n)_(n=1)^infinity$是正远离$0$的，所以$x y$是正的
  ]
]

#definition[实数的绝对值][
  $x$是实数，定义$abs(x)$为
  - $x$，当$x$是正的
  - $0$，当$x$是$0$
  - $-x$，当$x$是负的
]

#definition[实数的序][
  $x,y in RR$

  + $x > y <=> x - y$是正的
  + $x < y <=> x - y$是负的
  + $x >= y <=> x > y or x = y$
  + $x <= y <=> x < y or x = y$
]

#theorem[实数的序的基本性质][
  $x,y,z in RR$，下列成立
  + 实数的三歧性
  + $x > y <=> y < x$
  + $x <y and y < z => x < z$
  + $x < y => x + z < y + z$
  + $x < y and x$是正的$=> x z < y z$

  #proof[
    令$x = "LIM"_(n->infinity)a_n,y = "LIM"_(n->infinity)b_n,z = "LIM"_(n->infinity)c_n$
    + 见定理 5.38的证明
    + $x > y <=> y < x$
      - $=>$

        $x > y => x - y$是正的，那么$ exists c in QQ^+,forall i in ZZ^+, a_i - b_i >= c $于是$ exists c in QQ^+, forall i in ZZ^+, -(a_i - b_i) = b_i - a_i <= -c $其中$-c in QQ^-$，于是$y-x$是负的，所以$y < x$

      - $arrow.double.l$

        $y < x => y - x$是负的，那么$ exists -c in QQ^-, forall i in ZZ^+, b_i - a_i <= -c $于是$ exists -c in QQ^-, forall i in ZZ^+, -(b_i - a_i) = a_i - b_i <= -(-c) = c $其中$c in QQ^+$，于是$x - y$是正的，那么$x > y$
    + $x <y and y < z => x < z$

      $x < y => x - y$是负的，所以有$ exists -d_1 in QQ^-, forall i in ZZ^+, a_i - b_i <= -d_1 $ $y < z => y -z$是负的，于是$ exists -d_2 in QQ^-, forall i in ZZ^+, b_i - c_i <= -d_2 $所以有$ forall i in ZZ^+, a_i -b_i + b_i -c_i = a_i -c_i <= -d_1 - d_2 $其中$-d_1-d_2 in QQ^-$，所以$x - z$是负的，所以$x < z$

    + $x < y => x+z < y+z$

      $x < y => x - y$是负的，于是$ exists -d in QQ^-, forall i in ZZ^+, a_i - b_i <= -d $所以有$ a_i-b_i + c_i-c_i=a_i+c_i - b_i - c_i <= -d $所以$x+z - (y+z)$是负的，所以$x+z < y+z$

    + $x < y and z$是正的$=> x z < y z$

      $x < y => x- y$是负的，于是$ exists -d_1 in QQ^-, forall i in ZZ^+, a_i - b_i <= -d_1 < 0 $由于$z$是正的，那么$ exists d_2 in QQ^+, forall i in ZZ^+, c_i >= d_2 > 0 $对$c_i >= d_2$乘以负数$a_i-b_i$，不等式反转，所以有$ c_i (a_i - b_i) <= d_2(a_i-b_i) <= -d_1 d_2 $其中$-d_1 d_2 in QQ^-$所以$x z - y z$是负的，所以$x z < y z$
  ]

  #note-block[
    这里证明的性质也是有理数的序的性质
  ]
]

#lemma[$x in RR^+ => x^(-1) in RR^+$][
  #proof[
    $x$是正实数，且$x x^(-1)=1$，易知$x^(-1)!=0$；如果$x^(-1)$是负的，那么$x x^(-1)$也是负的，矛盾，由实数的三歧性，$x^(-1)$是正的
  ]
]

#lemma[$y in RR^+, x in RR, x > y => x^(-1) < y^(-1)$][
  由于$y$是正的，那么$x > y=> x$也是正的，假设$x^(-1) >= y^(-1)$，就有$ 1 = x x^(-1) > y x^(-1) >= y y^(-1) = 1 $于是$1 > 1$，矛盾，由实数的序的三歧性，$x^(-1) < y^(-1)$
]

#lemma[$(a_n)_(n=1)^infinity$是非负有理数组成的柯西序列，那么实数$x = "LIM"_(n->infinity)a_n$是非负实数][
  #proof[
    假设$x = "LIM"_(n->infinity)a_n$是负的，根据负实数的定义$x = "LIM"_(n->infinity)b_n$，其中$(b_n)_(n=1)^infinity$是负远离$0$的序列，所以$ exists -c in QQ^+, forall i in ZZ^+, b_i <= -c $但是条件中$(a_n)_(n=1)^infinity$是非负有理数组成的，那么$ forall i in ZZ^+, a_i >= 0 $于是$ forall i in ZZ^+, abs(a_i - b_i) >= c $所以序列$(a_n)_(n=1)^infinity$与$(b_n)_(n=1)^infinity$不等价，矛盾
  ]
]

#corollary[极限的保序性][
  $(a_n)_(n=1)^infinity$与$(b_n)_(n=1)^infinity$是有理数柯西序列，满足$forall i in ZZ^+, a_i >= b_i$，那么$"LIM"_(n->infinity)a_n >= "LIM"_(n->infinity)b_n$

  #proof[
    定义新序列$(a_n - b_n)_(n=1)^infinity$，由于$(a_n)_(n=1)^infinity$与$(b_n)_(n=1)^infinity$是有理数柯西序列，满足$ forall i in ZZ^+, a_i >= b_i $那么$ forall i in ZZ^+, a_i - b_i >= 0 $所以序列$(a_n - b_n)_(n=1)^infinity$是非负有理数组成的，那么$z = "LIM"_(n->infinity)(a_n-b_n)$是非负实数，令$x = "LIM"_(n->infinity)a_n, y = "LIM"_(n->infinity)b_n$，所以$x - y$是非负的，所以$x >= y$，所以$"LIM"_(n->infinity)a_n >= "LIM"_(n->infinity)b_n$
  ]

  #note-block[
    引理 2.46和推论 2.47表明，非负实数集合是闭的
  ]
]

#lemma[用有理数界定实数][
  $forall x in RR^+, exists q in QQ^+,N in ZZ^+, q<=x<=N$

  #proof[
    令$x = "LIM"_(n->infinity)a_n$，由于$x$是正的，那么$(a_n)_(n=1)^infinity$是正远离$0$的，所以有$ exists q in QQ^+, forall i in ZZ^+, a_i >= q > 0 $由于$(a_n)_(n=1)^infinity$是柯西序列，柯西序列是有界的，令界为$M in QQ^+$，就有$ forall i in ZZ^+, 0 < a_i <= M $由于$M$是有理数，先前证明了两个整数之间至少有一个有理数，不妨令$N = ceil(M)$，易知$N in ZZ^+ and N >= M$，于是就有$ forall i in ZZ^+, a_i <= M <= N $综上就有$ forall i in ZZ^+, q<= a_i <= N $所以有$ "LIM"_(n->infinity)q <= "LIM"_(n->infinity)a_n <= "LIM"_(n->infinity)N => q <= x <= N $
  ]
]

#corollary[阿基米德性质][
  $forall x in RR, forall epsilon in RR^+,exists M in ZZ^+, M epsilon > x$

  #proof[
    + 如果$x$是非正实数，那么取$M = 1$即可，$M epsilon = epsilon > 0 > x$
    + 如果$x$是正的，由于$epsilon in RR^+$，那么$x/epsilon in RR^+$，先前证明了可以用有理数界定实数，那么$exists N in ZZ^+, x/epsilon <= N$，令$M = N+1$，就有$ M epsilon = (N+1)epsilon = N epsilon + epsilon >= x + epsilon > x $于是确实存在$M in ZZ^+$，使得对任意的实数$x$和正实数$epsilon$满足$M epsilon > x$
  ]

  #note-block[
    这个推论说明，无论多大的实数$x$，无论多小的实数$epsilon$，都可以将小实数不断与自己相加，最终也是可以大于大实数的
  ]
]

#definition[取大/取小操作][
  $x, y in RR$，定义取大/取小操作分别为
  $
    max(x, y) = cases(x\, x>=y, y\, x<y)\
    min(x, y) = cases(x\, x<=y, y\, x>y)
  $
]

#lemma[取大/取小操作的性质][
  + $max(x, y) = -min(-x, -y)$
  + $min(x, y) = -max(-x, -y)$
  + $max(x, y) = max(y, x)$
  + $max(x, x)=x$
  + $z in RR, max(x+z, y+z) = max(x, y)+z$
  + $z in RR and z>=0, max(x z, y z) = z max(x, y)$
  + $z in RR and z <0, max(x z, y z) = z min(x, y)$
  + $min(x, y) = min(y, x)$
  + $min(x, x)=x$
  + $z in RR, min(x+z, y+z) = min(x, y)+z$
  + $x, y in RR^+, max(x, y)^(-1) = min(x^(-1), y^(-1))$
  + $x, y in RR^+, min(x, y)^(-1) = max(x^(-1), y^(-1))$
]

#practice-separate()

#problem[证明实数的三歧性和正实数的基本性质][
  见定理 2.39、引理 2.40和引理 2.41的证明
]

#problem[证明实数的序也满足有理数的序的性质][
  见定理 2.44的证明
]

#problem[$forall x in RR, exists! N in ZZ, N <= x < N+1$][

  + 存在性
    + $x in RR^+$

      $x in RR^+ => exists q in QQ^+, N in ZZ^+,q <= x <= N$，那么令集合$S = {n in ZZ^+: n>x}$，易知这是一个自然数的子集，那么一定存在一个最小元素$m = min(S)$，所以有$m > x$

      如果$m - 1 > x$，则与最小元素矛盾，所以根据实数序的三歧性，只能是$m-1 <= x$，综上有$m-1<= x < m$，令$N = m-1$就有$N <= x < N+1$

    + $x = 0$，显然$0 <= 0 < 1$
    + $x in RR^-$

      $x in RR^- => -x in RR^+$，于是$ m <= -x < m+1 => -(m+1) < x <= -m $取$m = -N'$，就有$N'-1 < x <= N'$

      - 如果$x < N'$，则$N'-1<x<N' => N'-1<=x<N'$，令$N = N'-1$，就有$N <= x < N+1$
      - 如果$x = N'$，直接有$N' <= x < N'+1$，令$N = N'$，就有$N <= x < N+1$

    + 由实数的三歧性，考虑了所有情况，证明完毕

  + 唯一性

    假设$N_1,N_2 in ZZ$，都满足$ N_1 <= x < N_1 + 1\ N_2 <= x < N_2 + 1 $
    + 如果$N_1 > N_2$，就有$N_1 >= N_2 + 1$，于是$ N_2 <= x < N_2 + 1 <= N_1 <= x => x < x $矛盾
    + 如果$N_1 < N_2$，就有$N_1 + 1 <= N_2$，于是$ x < N_1 + 1 <=N_2 <= x => x < x $矛盾
    + 由整数的三歧性，只能是$N_1 = N_2$，所以唯一性得证

  #note-block[
    + 比较麻烦的地方是存在性证明中处理不等号中取等的位置，在负数的考虑中不等式反转导致位置到了其他地方，所以非要啰嗦几句，具体来说就是$x > y => x >= y$，这是因为$>=$的意思是大于或等于

    + 上面证明了这样的$N$存在且唯一，所以可以将向上/向下取整也迁移到实数上$forall x in R, N = floor(x), N<= x < N+1$
  ]
]

#problem[$forall x in RR^+, exists N in ZZ^+, x > 1/N > 0$][
  $x in RR^+ => 1/x in RR^+$，那么$ exists N' in ZZ^+, N'+1 > 1/x >= N' $于是$ 1/N' >= x > 1/(N'+1) > 0 $令$N = N'+1， N in ZZ^+$，就有$ x > 1/N > 0 $

  #note-block[
    无论多么小的一个正实数，总能找到一个超大的正整数，使得正整数的倒数比超小正实数还小，但还是比零大
  ]
]

#problem[$x, y in RR and x < y => exists q in QQ, x < q <y$][
  $
    y > x & => y - x > 0 \
          & => exists N in ZZ^+, N(y-x) > 1 \
          & => y-x > 1/N
  $
  由于$N x$也是一个实数，那么$ exists M in ZZ, M <= N x < M+1 => M/N <= x < (M+1)/N $所以有$ y = y-x+x > 1/N + M/N = (M+1)/N $综上就有$ x < (M+1)/N < y $取$q = (M+1)/N$，易知$q$是有理数，所以确实存在有理数使得$x < q < y$

  #note-block[
    有理数在实数中也是稠密的
  ]
]

#problem[$x, y in RR, epsilon in RR^+$，证明$abs(x - y) < epsilon <=>-epsilon + y< x < epsilon+y$，证明$abs(x - y) <= epsilon <=> -epsilon + y<= x <= epsilon + y$][
  + $abs(x - y) < epsilon <=>-epsilon + y< x < epsilon+y$
    - $=>$
      + $x - y$是正的，那么$abs(x - y) = x - y < epsilon => x < epsilon + y$，而且$x - y > 0 => 0 + x > -epsilon + y$，所以$-epsilon + y < x < epsilon + y$
      + $x - y$是负的，那么$abs(x - y) = -(x - y) < epsilon => x - y > -epsilon => x > -epsilon + y$，而且$x - y < 0 => 0 + x <epsilon + y$，所以$-epsilon + y < x < epsilon + y$
      + $x - y$是$0$，那么$abs(x - y) = 0 < epsilon$，直接有$-epsilon < 0 < epsilon$
      + 由实数的三歧性，$abs(x - y) < epsilon => -epsilon + y < x < epsilon + y$

    - $arrow.double.l$

      由于$-epsilon + y < x < epsilon + y => -epsilon < x - y < epsilon$，那么$x - y < epsilon and y - x < epsilon$，那么根据绝对值定义$ abs(x - y) = cases(x - y\, x - y>=0, y-x\, x-y<0) $总有$abs(x - y) < epsilon$

  + $abs(x - y) <= epsilon <=> -epsilon + y<= x <= epsilon + y$

    证明同上
]

#problem[证明：$forall x, y in RR, forall epsilon in RR^+, x <= y + epsilon <=> x <= y$；证明：$forall epsilon in RR^+, abs(x - y) <= epsilon <=> x = y$][

  + $forall x, y in RR, forall epsilon in RR^+, x <= y + epsilon <=> x <= y$
    - $=>$

      只需要证明推出$x>y$是矛盾的即可，假设$x > y$，那么$x - y > 0$，取$epsilon = (x-y)/2 in RR^+$，由于$forall epsilon in RR^+ ,x <= y + epsilon$，那么就有$    x & <= y + (x-y)/2 \
      => x & <= (x+y)/2 $由于$ x > y => x + x > y + x => x > (x+y)/2 $那么就有$ x <= (x+y)/2 < x => x < x $矛盾，所以不可能得到$x > y$，所以一定是$ x <= y $

    - $arrow.double.l$

      $forall epsilon in RR^+, y < y + epsilon$，所以有$x <= y < y + epsilon => x < y + epsilon => x <= y + epsilon$

  + $forall epsilon in RR^+, abs(x - y) <= epsilon <=> x = y$

    - $=>$

      $forall epsilon in RR^+, abs(x - y) <= epsilon => -epsilon<= x - y<= epsilon$
      - 假设$x > y$，那么就有$x - y > 0$，令$epsilon = (x - y)/2 in RR^+$，那么就有$ x - y <= epsilon = (x-y)/2 => x - y <= 0 $与$x > y$矛盾
      - 假设$x < y$，那么就有$y-x>0$，令$epsilon = (y - x)/2 in RR^+$，那么就有$ x - y >= -epsilon = (x-y)/2 => x - y >=0 $与$x < y$矛盾
      - 综上，由实数序的三歧性，只能是$x = y$

    - $arrow.double.l$

      $x = y => x - y = 0$，由于$forall epsilon in RR^+,epsilon > 0 = x - y = abs(x - y)$，所以有$abs(x - y) < epsilon => abs(x - y) <= epsilon$
]

#problem[$(a_n)_(n=1)^infinity$是有理数柯西序列，$x in RR$，证明$forall i in ZZ^+, a_i <= x => "LIM"_(n->infinity)a_n <= x$，证明$forall i in ZZ^+, a_i >= x => "LIM"_(n->infinity)a_n >= x$][

  #proof[
    由于$(a_n)_(n=1)^infinity$是柯西序列，那么$y = "LIM"_(n->infinity)a_n, y in RR$，由于$x in RR$，那么令$x = "LIM"_(n->infinity)b_n, (b_n)_(n=1)^infinity$是柯西序列

    + $forall i in ZZ^+, a_i <= x => "LIM"_(n->infinity)a_n <= x$
      假设推出$y = "LIM"_(n->infinity)a_n > x => y - x > 0$，那么一定存在一个有理数，满足$(y-x)/2 > q > 0$，那么令$epsilon = q > 0$，由于$(a_n)_(n=1)^infinity$是柯西序列，那么$ exists N in ZZ^+, forall i >= N, abs(a_i - y) <= epsilon = q < (x-y)/2 $于是$ a_i >= -(y-x)/2 + y = (x+y)/2 > x $与$forall i in ZZ^+, a_i <= x$矛盾，所以只能是$"LIM"_(n->infinity)a_n <= x$

    + $forall i in ZZ^+, a_i >= x => "LIM"_(n->infinity)a_n >= x$

      同理可证
  ]

  #note-block[
    + 在证明的时候，对于$epsilon$的选取，只要是一个小于等于$(y-x)/2$的有理数即可，格外的强调是有理数的原因是：目前可使用的柯西序列的定义中，$epsilon$只能在正有理数中
    + 关于$abs(a_i - y) <= epsilon$这个表述，这个看起来好像是在进行柯西序列和一个常数列等价的判定，但是$y$有可能不是有理数，而我们现在的柯西序列都是定义在有理数序列上，所以感觉上这么写是有问题的。_但是_，这个式子的意思是在对一个有理数与实数之差的绝对值进行不等式比较，而实数的绝对值的性质在问题 2.57中已经进行了证明，所以是没问题的。
  ]
]

#problem[证明取大取小操作的性质][
  #proof[
    + $max(x, y) = -min(-x, -y)$
      - $x >= y => -y >= -x$，那么$   & max(x, y) = x \
        - & min(-x, -y) =-(-x) = x $所以$max(x, y) = -min(-x, -y)$
      - $x < y => -y < -x$，那么$   & max(x, y) = y \
        - & min(-x, -y) = -(-y) = y $所以$max(x, y) = -min(-x, -y)$
      - 综上，由实数三歧性，都有$max(x, y) = -min(-x, -y)$

    + $min(x, y)=-max(-x, -y)$
      - $x <= y => -y <= -x$，那么$   & min(x, y) = x \
        - & max(-x, -y) = -(-x) = x $于是$min(x, y) = -max(-x, -y)$
      - $x > y => -y > -x$，那么$   & min(x, y) = y \
        - & max(-x, -y) = -(-y) =y $于是$min(x, y) = -max(-x, -y)$
      - 综上，由实数三歧性，都有$min(x, y) = -max(-x, -y)$

    + $max(x, y) = max(y, x)$
      - $x >= y => y<=x$，那么$max(x, y) = x$，那么$max(y, x) = x$，于是$max(x, y) = max(y, x)$
      - $x < y => y > x$，那么$max(x, y) = y$，那么$max(y, x) =y$，于是$max(x, y) = max(y, x)$
      - 综上，由实数三歧性，都有$max(x, y) = max(y, x)$

    + $max(x, x) = x$

      $x = x => x <= x$，那么$max(x, x) = x$

    + $z in RR, max(x+z, y+z) = max(x, y)+z$
      - $x >= y => x + z >= y + z$，那么$ & max(x + z, y+z) = x+z \
        & max(x, y) + z = x + z $于是$max(x + z, y + z) = max(x, y) + z$
      - $x < y => x + z < y + z$，那么$ & max(x + z, y + z) = y + z \
        & max(x, y) + z = y + z $于是$max(x + z, y + z) = max(x, y) + z$
      - 综上，由实数三歧性，都有$max(x + z, y+z) = max(x, y) + z$

    + $z in RR and z>=0, max(x z, y z) = z max(x, y)$
      - $z >= 0 and x>=y => x z >= y z$，那么$ & max(x z, y z) = x z \
        & z max(x, y) = z x $于是$z >=0, max(x z, y z) = z max(x, y)$
      - $z >= 0 and x < y => x z <= y z$于是$ & max(x z, y z) = y z \
        & z max(x, y) = z y $于是$z >=0, max(x z, y z) = z max(x, y)$
      - 综上，由实数三歧性，都有$z >= 0, max(x z, y z)= z max(x, y)$

    + $z in RR, z < 0, max(x z, y z) = z min(x, y)$
      - $z < 0, x >= y => x z <= y z$，那么$ & max(x z, y z) = y z \
        & z min(x, y) = z y $于是$z < 0, max(x z, y z) = z min(x, y)$
      - $z < 0, x < y => x z > y z$，那么$ & max(x z, y z) = x z \
        & z min(x, y) = z x $于是$z < 0, max(x z, y z) = z min(x, y)$
      - 综上，由实数三歧性，都有$z < 0, max(x z, y z) = z min(x, y)$

    + $min(x, y) = min(y, x)$
      - $x >= y => y <= x$，那么$ & min(x, y) = y \
        & min(y, x) = y $于是$min(x, y) = min(y, x)$
      - $x < y => y > x$，那么$ & min(x, y) = x \
        & min(y, x) = x $于是$min(x, y) = min(y, x)$
      - 综上，由实数三歧性，都有$min(x, y) = min(y, x)$

    + $min(x, x)=x$

      $x = x => x <= x$，于是$min(x, x) = x$

    + $z in RR, min(x+z, y+z) = min(x, y) + z$
      - $x >= y => x + z >= y + z$，那么$ & min(x+z, y+z) = y+z \
        & min(x, y)+z = y + z $于是$min(x+z, y+z) = min(x, y)+z$
      - $x < y => x + z< y +z$，那么$ & min(x+z, y+z) = x+z \
        & min(x, y)+z = x + z $于是$min(x+z, y+z)=min(x, y)+z$
      - 综上，由实数三歧性，都有$min(x+z, y+z)=min(x, y)+z$

    + $x, y in RR^+, max(x, y)^(-1) = min(x^(-1), y^(-1))$
      - $x, y in RR^+, x >=y => x^(-1) <= y^(-1)$那么$ & max(x, y)^(-1) = x^(-1) \
        & min(x^(-1), y^(-1)) = x^(-1) $于是$max(x, y)^(-1) = min(x^(-1), y^(-1))$
      - $x, y in RR^+, x <y => x^(-1) > y^(-1)$那么$ & max(x, y)^(-1) = y^(-1) \
        & min(x^(-1), y^(-1)) = y^(-1) $于是$max(x, y)^(-1) = min(x^(-1), y^(-1))$
      - 综上，由实数三歧性，都有$max(x, y)^(-1) = min(x^(-1), y^(-1))$

    + $x, y in RR^+, min(x, y)^(-1) = max(x^(-1), y^(-1))$
      - $x,y in RR^+,x >= y, x^(-1) <= y^(-1)$那么$ & min(x, y)^(-1) = y^(-1) \
        & max(x^(-1), y^(-1)) = y^(-1) $于是$min(x, y)^(-1) = max(x^(-1), y^(-1))$
      - $x, y in RR^+, x < y => x^(-1) > y^(-1)$那么$ & min(x, y)^(-1) = x^(-1) \
        & max(x^(-1), y^(-1)) = x^(-1) $于是$min(x, y)^(-1) = max(x^(-1), y^(-1))$
      - 综上，由实数三歧性，都有$min(x, y)^(-1) = max(x^(-1), y^(-1))$
  ]

  #note-block[
    关于取大取小操作的定义与性质，原书中是以课后题的形式出现的，这里单另整理为了一条定义、一系列性质与对性质的证明（即本习题）
  ]
]
== 最小上界性质


// #lemma[$forall x in RR^+, exists N in ZZ^+, x > 1/N >0$][]

// #corollary[两个实数之间至少有一个有理数][
//   $x,y in RR, x>y => exists q in QQ, x < q < y$

//   #proof[
//     令$x = "LIM"_(n->infinity)a_n, y = "LIM"_(n->infinity)b_n$，由于$x< y$，那么$y-x$是正的，那么$exists c in QQ^+, forall i in ZZ^+, a_i - b_i >= c$
//   ]
// ]
