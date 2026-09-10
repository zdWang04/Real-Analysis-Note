#import "@preview/euler-math:0.1.0": *
#import "../utils/utils.typ": *


= 序列的极限

== 收敛与极限法则

#definition[实数的距离][
  $ forall x, y in RR, d(x, y) := abs(x-y) $
]

#definition[$epsilon$-接近的实数][

  $epsilon in RR^+, x, y in RR, x, y$是$epsilon$接近的$<=> d(x, y) <= epsilon$
]

#definition[实数柯西序列][
  $epsilon in RR^+, N in ZZ, (a_n)_(n=N)^infinity$是实数序列

  + $(a_n)_(n=N)^infinity$是$epsilon$-稳定的$<=> forall j, k >= N, d(a_j, a_k) <= epsilon$
  + $(a_n)_(n=m)^infinity$是最终$epsilon$-稳定的$<=> exists N >= m, (a_n)_(n=N)^infinity$是$epsilon$-稳定的
  + $forall epsilon in RR^+, (a_n)_(n=m)^infinity$都是最终$epsilon$-稳定的$<=> (a_n)_(n=m)^infinity$是柯西序列

  #note-block[

    更加常见的定义是：

    $forall epsilon in RR^+, exists N in ZZ^+, forall j,k >= N, abs(a_j - a_k) <= epsilon <=> (a_n)_(n=m)^infinity$是柯西序列
  ]
]

#note-block[
  $(a_n)_(n=m)$是索引从$m$开始的有理数序列，那么$(a_n)_(n=m)$是有理数版定义下的柯西序列，当且仅当它也是实数版定义下的柯西序列

  #proof[
    - 考虑该序列是实数版定义下的柯西序列，那么就有$ forall epsilon in RR^+, exists N >= m, forall j,k >= N, abs(a_j - a_k) <= epsilon $由阿基米德性质$exists epsilon' in QQ^+, epsilon' > epsilon$，那么就有$ exists N >= m, forall j,k >= N, abs(a_j - a_k) <= epsilon < epsilon' $这正是有理数版定义下的柯西序列
    - 考虑该序列是有理数版定义下的柯西序列，那么就有$ forall epsilon in QQ^+, exists N >= m, forall j, k >= N, abs(a_j - a_k) <= epsilon $仍然由阿基米德性质，$exists epsilon' in RR^+, epsilon < epsilon'$，那么就有$ exists N >= m, forall j, k >= N, abs(a_j - a_k) <= epsilon < epsilon' $这正是实数版定义下的柯西序列
  ]
]

#definition[序列的收敛][
  $epsilon in RR^+, L in RR$
  + 实数序列$(a_n)_(n = N)^infinity$是$epsilon$-接近于$L$的$<=> forall n>= N, abs(a_n - L) <= epsilon$，即$forall n >=N, a_n$都是$epsilon$-接近于$L$的
  + 实数序列$(a_n)_(n = m)^infinity$是最终$epsilon$-接近于$L$的$<=>exists N >= m, (a_n)_(n=N)^infinity$是$epsilon$-接近于$L$的
  + 实数序列$(a_n)_(n = m)^infinity$收敛于$L <=> forall epsilon in RR^+, (a_n)_(n = m)^infinity$都是最终$epsilon$-接近于$L$

  #note-block[
    更加常见的定义是：

    $L in RR, (a_n)_(n=m)^infinity$是实数序列，如果
    $ forall epsilon in RR^+, exists N >= m, forall j >= N, abs(a_j - L) <= epsilon $那么称$(a_n)_(n=m)^infinity$收敛于$L$
  ]
]

#theorem[不可能收敛到两个不同的实数][
  $(a_n)_(n=m)^infinity$是实数序列，$L, L' in RR, L != L'$，那么$(a_n)_(n=m)^infinity$不可能同时收敛于$L,L'$

  #proof[
    取$epsilon = abs(L-L')/3$，由于$L != L'$，那么$abs(L - L') > 0$，假设$(a_n)_(n=m)^infinity$同时收敛于$L, L'$，那么有
    $ exists M_1 >= m, forall i >= M_1, abs(a_i - L) <= epsilon\
    exists M_2 >= m, forall i >= M_2, abs(a_i - L') <= epsilon $取$N = max(M_1, M_2)$，那么$ & forall i >= N, abs(a_i - L) <= epsilon \
    & forall i >= N, abs(a_i - L') <= epsilon \ $于是就有$ & abs(a_i - L) + abs(a_i - L') <= 2/3 abs(L - L') \
    & => abs(L - L') <= 2/3 abs(L - L') \
    & => abs(L - L') <= 0 $矛盾，所以不可能同时收敛于两个不同的实数，也因此，极限唯一
  ]
]
#pagebreak()
#definition[极限的定义][
  $(a_n)_(n=m)^infinity$是实数序列，如果该序列收敛到实数$L$，那么称该序列收敛且极限为$L$，记作：
  $
    L = lim_(n->infinity)a_n
  $
  如果序列无法收敛到任何实数，则称该序列_发散_，且令$lim_(n->infinity)a_n$为未定义

  #note-block[
    定理 6.5保证了如果极限存在，则极限必定唯一
  ]
]

#example[$lim_(n->infinity)1/n = 0$][
  #proof[
    取$epsilon in RR^+$，那么$ abs(1/n - 0) = 1/n <= epsilon => n >= 1/epsilon $取$N=ceil(1/epsilon)$，那么$ forall n >= N, 1/n < epsilon $所以$(1/n)_(n=1)^infinity$收敛于$0$，因此其极限是$0$
  ]
]

#lemma[收敛序列也是柯西序列][
  $(a_n)_(n=m)^infinity$是实数序列，且$lim_(n->infinity)a_n = L$，那么$(a_n)_(n=m)^infinity$也是柯西序列

  #proof[
    由于$lim_(n->infinity)a_n = L$，那么有$ forall epsilon in RR^+, exists N >=m, forall i >= N, abs(a_i - L) <= epsilon $任取$j,k>=N$，于是有
    $ & "    "abs(a_j - L) <= epsilon, abs(a_k - L) <= epsilon \
    & => abs(a_j - a_k) <= abs(a_j - L) + abs(L - a_k) <= 2 epsilon $所以$(a_n)_(n=m)^infinity$也是柯西序列
  ]
]

// #lemma[形式极限是极限][
//   如果$(a_n)_(n=1)^infinity$是一个有理数柯西序列，那么$(a_n)_(n=1)^infinity$收敛到$"LIM"_(n->infinity)a_n$，即$ "LIM"_(n->infinity)a_n = lim_(n->infinity)a_n $
// ]

#definition[有界序列][
  + 实数序列$(a_n)_(n=m)^infinity$以实数$M$为界$<=> forall n>=m, abs(a_n) <= M$
  + 实数序列$(a_n)_(n=m)^infinity$是有界的$<=> exists M in RR^+, forall n>=m, abs(a_n) <= M$
]

#corollary[所有收敛实数序列都是有界的]
#theorem[极限定律][
  $(a_n)_(n=m)^infinity, (b_n)_(n=m)^infinity$都是收敛的实数序列，$x, y in RR$，令$x := lim_(n->infinity)a_n, y := lim_(n->infinity)b_n$
  + 序列$(a_n+b_n)_(n=m)^infinity$收敛到$x + y$
    $ lim_(n->infinity)(a_n + b_n) = lim_(n->infinity)(a_n) + lim_(n->infinity)(b_n) $
  + 序列$(a_n b_n)_(n=m)^infinity$收敛到$x y$
    $ lim_(n->infinity)(a_n b_n) = lim_(n->infinity)a_n lim_(n->infinity)b_n $
  + $forall c in RR$，序列$(c a_n)_(n=m)^infinity$收敛到$c x$
    $ lim_(n->infinity)(c a_n)= c lim_(n->infinity)a_n $
  + 序列$(a_n-b_n)_(n=m)^infinity$收敛到$x-y$
    $ lim_(n->infinity)(a_n - b_n) = lim_(n->infinity)a_n - lim_(n->infinity)b_n $
  + 当$y != 0$且$forall n>=m,b_n != 0$时，序列$(b_n^(-1))_(n=m)^infinity$收敛到$y^(-1)$
    $ lim_(n->infinity)b_n^(-1) = (lim_(n->infinity)b_n)^(-1) $
  + 当$y != 0$且$forall n>=m,b_n != 0$时，序列$(a_n / b_n)_(n=m)^infinity$收敛到$x/y$
    $ lim_(n->infinity)(a_n/b_n) = (lim_(n->infinity)a_n) / (lim_(n->infinity)b_n) $
  + 序列$(max(a_n, b_n))_(n=m)^infinity$收敛到$max(x, y)$
    $ lim_(n->infinity)max(a_n, b_n) = max(lim_(n->infinity)a_n, lim_(n->infinity)b_n) $
  + 序列$(min(a_n, b_n))_(n=m)^infinity$收敛到$min(x, y)$
  $ lim_(n->infinity)min(a_n, b_n) = min(lim_(n->infinity)a_n, lim_(n->infinity)b_n) $
]

#practice-separate()

#problem[$(a_n)_(n=0)^infinity$是实数序列，且$forall n in NN, a_(n+1) > a_n$，证明：$forall m,n in NN, m> n => a_m > a_n$][
  #proof[
    由于$m, n in NN$，并且$m > n$，那么$m >= n+1$，令$k := m - n >= 1$，对$k$进行归纳
    - 当$k = 1$时，$m = n$，显然有$a_m = a_(n+1) > a_n$
    - 现在归纳性的假设$k$时成立，即有
      $ a_(m) = a_(n+k) > a_(n) $
    - 接下来证明$k+1$的情况，所以有
      $ a_(m+1) = a_(n+k+1) > a_(n+k) > a_(n) $因此$forall k >= 1, a_(n+k) > a_n$即$forall m > n, a_m > a_n$
  ]
]

#problem[$(a_n)_(n=m)^infinity$是实数序列，$L$是实数，那么$(a_n)_(n=m)^infinity$收敛到$L$，当且仅当，对于任意正实数$epsilon$，都存在正整数$N >=m$，满足$forall n >= N, abs(a_n - L) <= epsilon$][
  这个证明实际上就是将实数序列与实数的最终$epsilon$-稳定性的定义展开
]

#problem[$(a_n)_(n=m)^infinity$是实数序列，$c in RR$，令整数$m'>m$，那么$(a_n)_(n=m)^infinity$收敛到$c$，当且仅当$(a_n)_(n=m')^infinity$收敛到$c$][
  - $=>$

    由于$(a_n)_(n=m)^infinity$收敛到$c$，那么
    $ forall epsilon in RR^+, exists N_0 >= m, forall j>=N, abs(a_j - c) <= epsilon $取$N = max(N_0, m')$，那么$N >= m'$，于是有$ forall j >= N, abs(a_j - c) <= epsilon $
    这也是序列$(a_n)_(n=m')^infinity$收敛到$c$的定义
  - $arrow.double.l$

    由于$(a_n)_(n=m')^infinity$收敛到$c$，那么
    $ forall epsilon in RR^+, exists N >= m', forall j >= N, abs(a_j - c) <= epsilon $由于$m' > m$，那么$N > m$，于是$ forall j >= N, abs(a_j - c) <= epsilon $这也是序列$(a_n)_(n=m)^infinity$收敛到$c$的定义
]

#problem[$(a_n)_(n=m)^infinity$是实数序列，$c in RR, k in ZZ_(>=0)$，那么$(a_n)_(n=m)^infinity$收敛到$c$，当且仅当$(a_(n+k))_(n=m)^infinity$收敛到$c$][
  #proof[

    由于$k>=0$，当$k=0$时，二者为完全相同的序列，所以会收敛到同样的实数

    当$k > 0$时，$n+k > n$，所以$(a_(n+k))_(n=m)^infinity$与序列$(a_n)_(n=m+k)^infinity$是同一个序列，令$m' = m+k$，就有$m' > m$，就得到了序列$(a_n)_(n=m')^infinity$

    $(a_n)_(n=m')^infinity$与$(a_n)_(n=m)^infinity$收敛到同样的实数，这在前面已经证明过了
  ]
]

#note-block[
  问题 6.15和问题 6.16说明收敛序列的极限与索引以及开始位置关系不大，我们更关系的是极限过程下的长期行为
]

#problem[证明收敛序列也是柯西序列][见引理 6.8的证明]

#problem[证明形式极限就是正式极限][
  $(a_n)_(n=1)^infinity$是有理数柯西序列，那么$(a_n)_(n=1)^infinity$收敛到$"LIM"_(n->infinity)a_n$，即
  $
    "LIM"_(n->infinity)a_n = lim_(n->infinity)a_n
  $

  #proof[
    由于$(a_n)_(n=1)^infinity$是柯西序列，那么令实数$L := "LIM"_(n->infinity)a_n$，现在假设$(a_n)_(n=1)^infinity$不收敛到$L$，于是$ exists epsilon in RR^+, forall N >= 1, exists m >= N, abs(a_m -L) > epsilon $

    由于$(a_n)_(n=1)^infinity$是柯西序列，那么$ forall epsilon/2 in RR^+, exists N_0 >=1, forall j,k >= N_0, abs(a_j - a_k) <= epsilon/2 $


    - 由假设，$exists m_0 >= N_0, a_(m_0) - L > epsilon$，那么$ forall n >= N_0, abs(a_n - a_(m_0)) <= epsilon/2 => a_n >= -epsilon/2 + a_(m_0) > -epsilon/2 + L + epsilon = epsilon/2 + L $由形式极限的保序性就有$ "LIM"_(n->infinity)a_n = L > epsilon/2 + L => epsilon < 0 $矛盾
    - 由假设，$exists m_0 >= N_0, a_(m_0) - L < -epsilon$，那么$ forall n >= N_0, abs(a_n - a_(m_0)) <= epsilon/2 => a_n <= epsilon/2 + a_(m_0) < epsilon/2 + L -epsilon = -epsilon/2 + L $由形式极限的保序性就有$ "LIM"_(n->infinity)a_n = L < -epsilon/2 + L => epsilon < 0 $矛盾
    - 综上，$(a_n)_(n=1)^infinity$收敛到$L$
  ]

  #note-block[
    这个证明说明先前的形式极限可以被正式极限所替代了，因为它们的行为一致
  ]
]

#problem[证明实数有界序列的定义与先前有理数有界序列的定义是一致的][
  实数序列$(a_n)_(n=m)^infinity$是有理数版的有界序列，当且仅当它是实数版的有界序列

  #proof[
    - $=>$\
      $(a_n)_(n=m)^infinity$是有理数版的有界序列，那么$ exists M in QQ^+, forall j >= m, abs(a_j) <= M $由阿基米德性质，存在实数$M' >= M$，于是$ forall j >= m, abs(a_j) <= M <= M', M' in RR^+ $这正是实数版本的有界序列的定义
    - $arrow.double.l$\
      $(a_n)_(n=m)^infinity$是实数版的有界序列，那么$ exists M in RR^+, forall j >=m, abs(a_j) <= M $由阿基米德性质，存在正有理数$M' >= M$，于是$ forall j >= m, abs(a_j) <= M <= M', M' in QQ^+ $这正是有理数版本的有界序列的定义
  ]
]

#problem[证明极限定律][

  #proof[
    $(a_n)_(n=m)^infinity, (b_n)_(n=m)^infinity$都是收敛的实数序列，$x, y in RR$，令$x := lim_(n->infinity)a_n, y := lim_(n->infinity)b_n$

    + 序列$(a_n+b_n)_(n=m)^infinity$收敛到$x + y$

      由于$(a_n)_(n=m)^infinity$收敛到$x$，那么
      $
        forall epsilon/2 in RR^+, exists M_1 >= m, forall i >= M_1, abs(a_i - x) <= epsilon/2
      $

      由于$(b_n)_(n=m)^infinity$收敛到$y$，那么
      $
        forall epsilon/2 in RR^+, exists M_2 >= m, forall i >= M_2, abs(b_i - y) <= epsilon/2
      $
      $ forall i >= max(M_1, M_2) ,abs(a_i + b_i - (x + y)) <= abs(a_i - x) + abs(b_i - y) <= epsilon $于是序列$(a_n+b_n)_(n=m)^infinity$收敛到$x + y$

    + 序列$(a_n b_n)_(n=m)^infinity$收敛到$x y$\

      $a_n b_n - x y =a_n b_n + a_n y - a_n y - x y = a_n (b_n -y) + (a_n - x)y\
      => abs(a_n b_n - x y) = abs(a_n (b_n -y) + (a_n - x)y) <= abs(a_n)abs(b_n - y) + abs(y)abs(a_n - x)$

      由于$(a_n)_(n=m)^infinity$收敛到$y$，那么必然有界
      $ exists M in RR^+, forall n >= m, abs(a_n) <= M $由于$(b_n)_(n=m)^infinity$收敛到$y$，那么
      $ forall epsilon/(2M) in RR^+, exists N_1, forall n >= M_1, abs(b_n - y) <= epsilon/(2M) $
      由于$(a_n)_(n=m)^infinity$收敛到$y$，那么
      $ forall epsilon/(2(abs(y) + 1)) in RR^+, exists N_2 >= m, forall n >= N_2, abs(a_n - x) <= epsilon/(2(abs(y) + 1)) $于是结合最先的不等式就有
      $ forall n >= max(N_1, &N_2), abs(a_n b_n - x y) <= M epsilon/(2M) + abs(y) epsilon/(2(abs(y) + 1)) < epsilon/2 + epsilon/2 = epsilon $于是序列$(a_n b_n)_(n=m)^infinity$收敛到$x y$
      #note-block[
        最麻烦的地方在于凑配出$a_n b_n - x y$的不等式，此外在$epsilon$的选取也有技巧，另外值得注意的是$epsilon/(2(abs(y) + 1))$的选取，由于$abs(y)$可能为零，所以不能简单的使用$epsilon/(2 abs(y))$，而要用$epsilon/(2 (abs(y) + 1))$，搭配$abs(y)/(abs(y) + 1) < 1$即可得到结果
      ]
    + $forall c in RR$，序列$(c a_n)_(n=m)^infinity$收敛到$c x$
      - 若$c = 0$，那么$(c a_n)_(n=m)^infinity$为常序列$0,...,0,...$，显然收敛到$0 x = 0$
      - 若$c != 0$，由于$(a_n)_(n=m)^infinity$收敛到$y$，那么$ forall epsilon/abs(c) in RR^+, exists N >= m, forall i >= N, abs(c a_i - c x) = abs(c)abs(a_i - x) <= abs(c) epsilon/abs(c) = epsilon $于是$forall c in RR$，序列$(c a_n)_(n=m)^infinity$收敛到$c x$

    + 序列$(a_n-b_n)_(n=m)^infinity$收敛到$x-y$

      由(1)和(3)的证明，$ lim_(n->infinity)(a_n-b_n) = lim_(n->infinity)a_n + (-1) times lim_(n->infinity)b_n = x - y $于是序列$(a_n-b_n)_(n=m)^infinity$收敛到$x-y$

    + 当$y != 0$且$forall n>=m,b_n != 0$时，序列$(b_n^(-1))_(n=m)^infinity$收敛到$y^(-1)$

      由于$(b_n^(-1))_(n=m)^infinity$收敛到$y^(-1)$，那么取$epsilon = abs(y)/2 > 0$，就有$ & exists N_1 >= m, forall n >= N_1, abs(b_n - y) <= abs(y)/2 \
      & => abs(b_n)>= abs(y) - abs(b_n - y) >= abs(y)/2 \
      & => 1/abs(b_n) <= 2/abs(y) $

      对于序列$(b_n^(-1))_(n=m)^infinity$有$ forall epsilon in RR^+, exists N_2 >= m, forall n>= N_2, abs(b_n - y) <= epsilon abs(y)^2/2 $

      于是取$N = max(N_1, N_2)$，就有$ forall n >= N, abs(1/(b_n) - 1/y) = abs((y - b_n)/(b_n y)) <= epsilon abs(y)^2/abs(y) 2/abs(y) = epsilon $于是当$y != 0$且$forall n>=m,b_n != 0$时，序列$(b_n^(-1))_(n=m)^infinity$收敛到$y^(-1)$
    + 当$y != 0$且$forall n>=m,b_n != 0$时，序列$(a_n / b_n)_(n=m)^infinity$收敛到$x/y$

      由(2)和(5)的证明，$ lim_(n->infinity)(a_n/b_n) = lim_(n->infinity)a_n times lim_(n->infinity)b_n^(-1) = x/y $

    + 序列$(max(a_n, b_n))_(n=m)^infinity$收敛到$max(x, y)$
      - 如果$x > y$，那么取$delta = (x-y)/2 > 0$，那么$ exists N_1 >=m, forall i >= N_1, abs(a_i - x) <= delta => abs(a_i) >= x - delta = (x+y)/2 $对于相同的$epsilon$也有$ exists N_2 >= m, forall i >= N_2, abs(b_i - y) <= delta => abs(b_i) <= delta + y = (x+y)/2 $于是$ forall i >= N = max(N_1, N_2), abs(b_i) <= (x+y)/2 <= abs(a_i) $所以$lim_(n->infinity)max(a_n, b_n) = lim_(n->infinity)a_n = x = max(x, y)$
      - 如果$x = y$，那么序列$(a_n)_(n=m)^infinity$与序列$(b_n)_(n=m)^infinity$等价，所以$ lim_(n->infinity)max(a_n, b_n) = lim_(n->infinity)a_n = x = max(x, y) $
      - 如果$x < y$，那么取$delta = (y - x)/2$，同理可得$ lim_(n->infinity)max(a_n, b_n) = lim_(n->infinity)b_n = y = max(x, y) $

    + 序列$(min(a_n, b_n))_(n=m)^infinity$收敛到$min(x, y)$

      类似(7)的证明
  ]
]

#problem[序列$(a_n)_(n=m)^infinity$和$(b_n)_(n=m)^infinity$都是收敛序列，分别收敛到$x, y$，如果$(b_n)_(n=m)^infinity$收敛到$0$，那么$ lim_(n->infinity)(a_n/(b_n)) = (lim_(n->infinity)a_n)/(lim_(n->infinity)b_n) $会失效，为什么？][
  回顾对这个运算的证明，它依赖极限倒数的证明，对于倒数的证明$ lim_(n->infinity)(b_n^(-1)) = (lim_(n->infinity)b_n)^(-1) $的条件是——该序列不会收敛到$0$，如果$(b_n)_(n=m)^infinity$收敛到$0$，即$ forall epsilon in RR^+, exists N >= m, forall n >= N, abs(b_j - 0) = abs(b_j) <= epsilon => abs(1/b_j) >= epsilon $也即$(1/(b_n))_(n=m)^infinity$是发散的，发散的极限是未定义的，这导致了收敛到$0$的序列的倒数的极限是未定义的，进而导致了极限除法中使用收敛到$0$的极限作为分母会产生未定义的结果
]

#problem[证明有理数版本的等价柯西序列的定义与实数版本的柯西序列的定义是一致的][
  $(a_n)_(n=m)^infinity$和$(b_n)_(n=m)^infinity$是实数序列，那么它们是有理数版本的等价柯西序列，当且仅当它们是实数版本的等价柯西序列

  #proof[
    - $=>$\

      $(a_n)_(n=m)^infinity$和$(b_n)_(n=m)^infinity$是有理数版本的等价柯西序列，那么
      $ forall epsilon in QQ^+, exists N >= m, forall j >= N, abs(a_j - b_j) <= epsilon $由于有理数可以被嵌入到实数中，所以$epsilon in RR^+$，所以上面的定义就是实数版本的等价柯西序列

    - $arrow.double.l$\

      $(a_n)_(n=m)^infinity$和$(b_n)_(n=m)^infinity$是实数版本的等价柯西序列，那么
      $ forall epsilon in RR^+, exists N >= m, forall j >= N, abs(a_j - b_j) <= epsilon $那么由阿基米德性质，存在有理数$epsilon'$满足$0 < epsilon' <= epsilon$，于是$ exists N' >= m, forall j >= N', abs(a_j - b_j) <= epsilon' <= epsilon, epsilon' in QQ^+ $这正是有理数版本的等价柯西序列的定义
  ]

]

== 广义实数系
