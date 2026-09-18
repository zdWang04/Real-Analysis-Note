#import "@preview/theorion:0.6.0": *
#import cosmos.fancy: *
= 序列的极限

== 收敛与极限法则

#definition[实数的距离][
  $forall x, y in RR$，距离定义为：
  $ d(x, y) := abs(x-y) $
]

#definition[$epsilon$-接近的实数][

  $epsilon in RR^+, x, y in RR, x, y$是$epsilon$接近的$<=> d(x, y) <= epsilon$
]

#definition[实数柯西序列][
  $epsilon in RR^+, N in ZZ, (a_n)_(n=N)^infinity$是实数序列

  + $(a_n)_(n=N)^infinity$是$epsilon$-稳定的$<=> forall j, k >= N, d(a_j, a_k) <= epsilon$
  + $(a_n)_(n=m)^infinity$是最终$epsilon$-稳定的$<=> exists N >= m, (a_n)_(n=N)^infinity$是$epsilon$-稳定的
  + $forall epsilon in RR^+, (a_n)_(n=m)^infinity$都是最终$epsilon$-稳定的$<=> (a_n)_(n=m)^infinity$是柯西序列
]

#note-block[
  更加常见的定义是：

  $forall epsilon in RR^+, exists N in ZZ^+, forall j,k >= N, abs(a_j - a_k) <= epsilon <=> (a_n)_(n=m)^infinity$是柯西序列
]


#example[
  $(a_n)_(n=m)$是索引从$m$开始的有理数序列，那么$(a_n)_(n=m)$是有理数版定义下的柯西序列，当且仅当它也是实数版定义下的柯西序列
]
#proof[
  - 考虑该序列是实数版定义下的柯西序列，那么就有$ forall epsilon in RR^+, exists N >= m, forall j,k >= N, abs(a_j - a_k) <= epsilon $由阿基米德性质$exists epsilon' in QQ^+, epsilon' > epsilon$，那么就有$ exists N >= m, forall j,k >= N, abs(a_j - a_k) <= epsilon < epsilon' $这正是有理数版定义下的柯西序列
  - 考虑该序列是有理数版定义下的柯西序列，那么就有$ forall epsilon in QQ^+, exists N >= m, forall j, k >= N, abs(a_j - a_k) <= epsilon $仍然由阿基米德性质，$exists epsilon' in RR^+, epsilon < epsilon'$，那么就有$ exists N >= m, forall j, k >= N, abs(a_j - a_k) <= epsilon < epsilon' $这正是实数版定义下的柯西序列
]

#definition[序列的收敛][
  $epsilon in RR^+, L in RR$
  + 实数序列$(a_n)_(n = N)^infinity$是$epsilon$-接近于$L$的$<=> forall n>= N, abs(a_n - L) <= epsilon$，即$forall n >=N, a_n$都是$epsilon$-接近于$L$的
  + 实数序列$(a_n)_(n = m)^infinity$是最终$epsilon$-接近于$L$的$<=>exists N >= m, (a_n)_(n=N)^infinity$是$epsilon$-接近于$L$的
  + 实数序列$(a_n)_(n = m)^infinity$收敛于$L <=> forall epsilon in RR^+, (a_n)_(n = m)^infinity$都是最终$epsilon$-接近于$L$
]
#note-block[
  更加常见的定义是：

  $L in RR, (a_n)_(n=m)^infinity$是实数序列，如果
  $ forall epsilon in RR^+, exists N >= m, forall j >= N, abs(a_j - L) <= epsilon $那么称$(a_n)_(n=m)^infinity$收敛于$L$
]

#theorem[不可能收敛到两个不同的实数][
  $(a_n)_(n=m)^infinity$是实数序列，$L, L' in RR, L != L'$，那么$(a_n)_(n=m)^infinity$不可能同时收敛于$L,L'$
]<thm:uniqueness-of-real-limit>
#proof[
  取$epsilon = abs(L-L')/3$，由于$L != L'$，那么$abs(L - L') > 0$，假设$(a_n)_(n=m)^infinity$同时收敛于$L, L'$，那么有
  $ exists M_1 >= m, forall i >= M_1, abs(a_i - L) <= epsilon\
  exists M_2 >= m, forall i >= M_2, abs(a_i - L') <= epsilon $取$N = max(M_1, M_2)$，那么$ & forall i >= N, abs(a_i - L) <= epsilon \
  & forall i >= N, abs(a_i - L') <= epsilon \ $于是就有$ & abs(a_i - L) + abs(a_i - L') <= 2/3 abs(L - L') \
  & => abs(L - L') <= 2/3 abs(L - L') \
  & => abs(L - L') <= 0 $矛盾，所以不可能同时收敛于两个不同的实数，也因此，极限唯一
]

#definition[极限的定义][
  $(a_n)_(n=m)^infinity$是实数序列，如果该序列收敛到实数$L$，那么称该序列收敛且极限为$L$，记作：
  $
    L = lim_(n->infinity)a_n
  $
  如果序列无法收敛到任何实数，则称该序列_发散_，且令$lim_(n->infinity)a_n$为未定义
]

#note-block[
  @thm:uniqueness-of-real-limit 保证了极限是良定义的
]

#example[$lim_(n->infinity)1/n = 0$]
#proof[
  取$epsilon in RR^+$，那么$ abs(1/n - 0) = 1/n <= epsilon => n >= 1/epsilon $取$N=ceil(1/epsilon)$，那么$ forall n >= N, 1/n < epsilon $所以$(1/n)_(n=1)^infinity$收敛于$0$，因此其极限是$0$
]

#lemma[收敛序列也是柯西序列][
  $(a_n)_(n=m)^infinity$是实数序列，且$lim_(n->infinity)a_n = L$，那么$(a_n)_(n=m)^infinity$也是柯西序列
]<lem:convergent-implies-cauchy>
#proof[
  由于$lim_(n->infinity)a_n = L$，那么有$ forall epsilon in RR^+, exists N >=m, forall i >= N, abs(a_i - L) <= epsilon $任取$j,k>=N$，于是有
  $ & "    "abs(a_j - L) <= epsilon, abs(a_k - L) <= epsilon \
  & => abs(a_j - a_k) <= abs(a_j - L) + abs(L - a_k) <= 2 epsilon $所以$(a_n)_(n=m)^infinity$也是柯西序列
]



#definition[有界序列][
  + 实数序列$(a_n)_(n=m)^infinity$以实数$M$为界$<=> forall n>=m, abs(a_n) <= M$
  + 实数序列$(a_n)_(n=m)^infinity$是有界的$<=> exists M in RR^+, forall n>=m, abs(a_n) <= M$
]

#corollary[所有收敛实数序列都是有界的]<cor:convergent-real-seq-is-bounded>
#proof[
  $(a_n)_(n=m)^infinity$是一个收敛的实数序列，假设收敛到$L$，就有
  $ forall epsilon in RR^+, exists N >= m, forall n >= N, abs(a_n - L) <= epsilon => abs(a_n) <= epsilon + abs(L) $对于有限序列$(a_n)_(n=m)^(n=N)$，一定是有界的，令界为$M$，于是取$M' = max(M, epsilon + abs(L))$，可见$M'$是序列的一个界
]

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
]<thm:limit-law>

#problem[$(a_n)_(n=0)^infinity$是实数序列，且$forall n in NN, a_(n+1) > a_n$，证明：$forall m,n in NN, m> n => a_m > a_n$]
#proof[
  由于$m, n in NN$，并且$m > n$，那么$m >= n+1$，令$k := m - n >= 1$，对$k$进行归纳
  - 当$k = 1$时，$m = n$，显然有$a_m = a_(n+1) > a_n$
  - 现在归纳性的假设$k$时成立，即有
    $ a_(m) = a_(n+k) > a_(n) $
  - 接下来证明$k+1$的情况，所以有
    $ a_(m+1) = a_(n+k+1) > a_(n+k) > a_(n) $因此$forall k >= 1, a_(n+k) > a_n$即$forall m > n, a_m > a_n$
]

#problem[$(a_n)_(n=m)^infinity$是实数序列，$L$是实数，那么$(a_n)_(n=m)^infinity$收敛到$L$，当且仅当，对于任意正实数$epsilon$，都存在正整数$N >=m$，满足$forall n >= N, abs(a_n - L) <= epsilon$]
#proof[
  这个证明实际上就是将实数序列与实数的最终$epsilon$-稳定性的定义展开
]

#problem[$(a_n)_(n=m)^infinity$是实数序列，$c in RR$，令整数$m'>m$，那么$(a_n)_(n=m)^infinity$收敛到$c$，当且仅当$(a_n)_(n=m')^infinity$收敛到$c$]
#proof[
  - $=>$

    由于$(a_n)_(n=m)^infinity$收敛到$c$，那么
    $ forall epsilon in RR^+, exists N_0 >= m, forall j>=N, abs(a_j - c) <= epsilon $取$N = max(N_0, m')$，那么$N >= m'$，于是有$ forall j >= N, abs(a_j - c) <= epsilon $
    这也是序列$(a_n)_(n=m')^infinity$收敛到$c$的定义
  - $arrow.double.l$

    由于$(a_n)_(n=m')^infinity$收敛到$c$，那么
    $ forall epsilon in RR^+, exists N >= m', forall j >= N, abs(a_j - c) <= epsilon $由于$m' > m$，那么$N > m$，于是$ forall j >= N, abs(a_j - c) <= epsilon $这也是序列$(a_n)_(n=m)^infinity$收敛到$c$的定义
]

#problem[$(a_n)_(n=m)^infinity$是实数序列，$c in RR, k in ZZ_(>=0)$，那么$(a_n)_(n=m)^infinity$收敛到$c$，当且仅当$(a_(n+k))_(n=m)^infinity$收敛到$c$]
#proof[

  由于$k>=0$，当$k=0$时，二者为完全相同的序列，所以会收敛到同样的实数

  当$k > 0$时，$n+k > n$，所以$(a_(n+k))_(n=m)^infinity$与序列$(a_n)_(n=m+k)^infinity$是同一个序列，令$m' = m+k$，就有$m' > m$，就得到了序列$(a_n)_(n=m')^infinity$

  $(a_n)_(n=m')^infinity$与$(a_n)_(n=m)^infinity$收敛到同样的实数，这在前面已经证明过了
]

#note-block[
  以上两个问题说明收敛序列的极限与索引的开始位置没有关系，我们更关心的是极限过程下的长期行为
]

#problem[证明@lem:convergent-implies-cauchy][见@lem:convergent-implies-cauchy 的证明]

#problem[证明形式极限就是正式极限][
  $(a_n)_(n=1)^infinity$是有理数柯西序列，那么$(a_n)_(n=1)^infinity$收敛到$"LIM"_(n->infinity)a_n$，即
  $
    "LIM"_(n->infinity)a_n = lim_(n->infinity)a_n
  $
]
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

#problem[证明实数有界序列的定义与先前有理数有界序列的定义是一致的][
  实数序列$(a_n)_(n=m)^infinity$是有理数版的有界序列，当且仅当它是实数版的有界序列
]
#proof[
  - $=>$\
    $(a_n)_(n=m)^infinity$是有理数版的有界序列，那么$ exists M in QQ^+, forall j >= m, abs(a_j) <= M $由阿基米德性质，存在实数$M' >= M$，于是$ forall j >= m, abs(a_j) <= M <= M', M' in RR^+ $这正是实数版本的有界序列的定义
  - $arrow.double.l$\
    $(a_n)_(n=m)^infinity$是实数版的有界序列，那么$ exists M in RR^+, forall j >=m, abs(a_j) <= M $由阿基米德性质，存在正有理数$M' >= M$，于是$ forall j >= m, abs(a_j) <= M <= M', M' in QQ^+ $这正是有理数版本的有界序列的定义
]

#problem[证明@thm:limit-law]
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

#note-block[
  本题最麻烦的地方在于(2)中需要凑配出$a_n b_n - x y$的不等式，此外在$epsilon$的选取也有技巧，另外值得注意的是$epsilon/(2(abs(y) + 1))$的选取，由于$abs(y)$可能为零，所以不能简单的使用$epsilon/(2 abs(y))$，而要用$epsilon/(2 (abs(y) + 1))$，搭配$abs(y)/(abs(y) + 1) < 1$即可得到结果
]

#problem[序列$(a_n)_(n=m)^infinity$和$(b_n)_(n=m)^infinity$都是收敛序列，分别收敛到$x, y$，如果$(b_n)_(n=m)^infinity$收敛到$0$，那么$ lim_(n->infinity)(a_n/(b_n)) = (lim_(n->infinity)a_n)/(lim_(n->infinity)b_n) $会失效，为什么？]
#proof[
  回顾对这个运算的证明，它依赖极限倒数的证明，对于倒数的证明$ lim_(n->infinity)(b_n^(-1)) = (lim_(n->infinity)b_n)^(-1) $的条件是——该序列不会收敛到$0$，如果$(b_n)_(n=m)^infinity$收敛到$0$，即$ forall epsilon in RR^+, exists N >= m, forall n >= N, abs(b_j - 0) = abs(b_j) <= epsilon => abs(1/b_j) >= epsilon $也即$(1/(b_n))_(n=m)^infinity$是发散的，发散的极限是未定义的，这导致了收敛到$0$的序列的倒数的极限是未定义的，进而导致了极限除法中使用收敛到$0$的极限作为分母会产生未定义的结果
]

#problem[证明有理数版本的等价柯西序列的定义与实数版本的柯西序列的定义是一致的][
  $(a_n)_(n=m)^infinity$和$(b_n)_(n=m)^infinity$是实数序列，那么它们是有理数版本的等价柯西序列，当且仅当它们是实数版本的等价柯西序列
]
#proof[
  - $=>$\

    $(a_n)_(n=m)^infinity$和$(b_n)_(n=m)^infinity$是有理数版本的等价柯西序列，那么
    $ forall epsilon in QQ^+, exists N >= m, forall j >= N, abs(a_j - b_j) <= epsilon $由于有理数可以被嵌入到实数中，所以$epsilon in RR^+$，所以上面的定义就是实数版本的等价柯西序列

  - $arrow.double.l$\

    $(a_n)_(n=m)^infinity$和$(b_n)_(n=m)^infinity$是实数版本的等价柯西序列，那么
    $ forall epsilon in RR^+, exists N >= m, forall j >= N, abs(a_j - b_j) <= epsilon $那么由阿基米德性质，存在有理数$epsilon'$满足$0 < epsilon' <= epsilon$，于是$ exists N' >= m, forall j >= N', abs(a_j - b_j) <= epsilon' <= epsilon, epsilon' in QQ^+ $这正是有理数版本的等价柯西序列的定义
]

== 广义实数系

#definition[广义实数系][

  广义实数系是实数系$RR$加上两个额外元素$-infinity, +infinity$
  - 广义实数系记作$RR^*$
  - $-infinity, +infinity$不同于任何$RR$中的元素
  - 对于任意$RR^*$中的元素$x$
    - $x in RR <=> x$是有限的
    - $x = -infinity or x = +infinity <=> x$是无限的
]

#definition[广义实数的相反数][
  $forall x in RR^*$，如果：
  - $x in RR$，相反数为$-x$
  - $x = -infinity$，相反数定义为$-(-infinity) := +infinity$
  - $x = +infinity$，相反数定义为$-(+infinity) := -infinity$
]

#definition[广义实数系上的序][
  $x, y in RR^*$，称$x <= y$，当且仅当下列其一为真：
  - $x, y in RR and x <= y$
  - $x = -infinity$
  - $y = +infinity$
]

#property[广义实数系的序的性质][
  $x, y, z in RR^*$，有以下成立：
  - $x <= x$
  - $x < y , x = y, x > y$同时只有一个成立
  - $x <= y and y <= z => x <= z$
  - $x <= y => -x >= -y$
]<prop:extended-real-order-properties>

#definition[广义实数系的子集的上确界/下确界][

  1. $E subset.eq RR^*$，定义$E$的最小上界/上确界$sup(E)$为：
  - $E subset.eq RR$，那么$sup(E)$的定义如实数子集的上确界的定义
  - $-infinity in E and +infinity in.not E$，定义$sup(E) := sup(E without {-infinity})$，此时的定义亦如实数子集的上确界的定义
  - $+infinity in E$，定义$sup(E) := +infinity$

  2. $E subset.eq RR^*$，定义$E$的最小下界/下确界$inf(E)$为
  $ inf(E) := -sup(-E) $其中$-E := {-x : x in E}$

]

#property[广义实数系上/下确界的性质][
  $E subset.eq RR^*$，有下列成立
  - $forall x in E, x <= sup(E) and x >= inf(E)$
  - $M in RR^*$，是$E$的一个上界，那么$sup(E) <= M$
  - $M in RR^*$，是$E$的一个下界，那么$inf(E) <= M$
]<prop:extended-real-sup-inf-properties>


#problem[证明@prop:extended-real-order-properties]
#proof[
  $x, y, z in RR^*$
  + 自反性
    - 如果$x in RR$，即为实数的自反性
    - 如果$x = +infinity$，由定义$forall y in RR^*, y <= +infinity$总成立，所以$+infinity <= +infinity$
    - 如果$x = -infinity$，由定义$forall y in RR^*, -infinity <= y$总成立，所以$-infinity <= -infinity$
  + 三歧性
    - 如果$x = +infinity$
      - $y = +infinity$，那么$y = x$
      - $y = -infinity$，由定义$forall x in RR^*, -infinity <= x$，于是$y <= x and y != x$，所以$y < x$
      - $y in RR$，再由定义$y <= +infinity and y != +infinity$，那么$y < x$
    - 如果$x = -infinity$
      - $y = -infinity$，那么$x = y$
      - $y = +infinity$，那么$x <= y and x != y$，那么$x < y$
      - $y in RR$，那么$x = -infinity < y$
    - 如果$x in RR and y in {+infinity, -infinity}$
      - $y = -infinity$，那么$x > y$
      - $y = +infinity$，那么$y > x$
    - 如果$x in RR and y in RR$，这种情况在实数的三歧性中业已证明
  + 传递性
    由于$x <= y and y <= z$
    - $x = -infinity$，那么总有$x = -infinity <= z$
    - $x = +infinity$，由于$x <= y$，那么$y = +infinity$，由于$y <= z$，那么$z = +infinity$，于是$x <= z$
    - $x in RR$
      - $y in RR or y = +infinity$
        - $(z in RR and y <= z )or z = +infinity$，无论那种情况，都有$x <= z$
  + 相反数反号
    - $x = -infinity$，那么$-x = +infinity$，总有$-x >= -y$
    - $y = +infinity$，那么$-y = -infinity$，总有$-x >= -y$
    - $x,y in RR$，由实数的序的性质可证
]

#problem[证明@prop:extended-real-sup-inf-properties]
#proof[
  $E subset.eq RR^*$
  + $forall x in E, x <= sup(E) and x >= inf(E)$
    - $+infinity in E and -infinity in.not E$
      - 那么$sup(E) = +infinity$，总有$forall x in E, sup(E) >= x$
      - 由于$+infinity in E and -infinity in.not E$，那么$+infinity in.not -E and -infinity in -E$，由于$ inf(E) = -sup(-E without {-infinity}) $于是
      $
        & forall x in E, -x in -E, -x <= sup(-E without {-infinity}) \
        & => x >= -sup(-E without {-infinity}) = inf(E)
      $
    - $-infinity in E and +infinity in.not E$
      - $sup(E) = sup(E without {-infinity}) in RR$，于是
        $ forall x in E & => x = -infinity or x in E without {-infinity} \ $

        如果$x = -infinity$，那么一定也有$x < sup(E)$

        如果$x in E without {-infinity}$，那么$x <= sup(E without {-infinity}) = sup(E)$
      - $inf(E) = -sup(-E) = -infinity$，易有$x <= inf(E)$
    - $-infinity in E and +infinity in E$
      易有$sup(E) = +infinity, inf(E) = -sup(-E) = -infinity$，于是总有$forall x in E, x <= sup(E), x >= inf(E)$
    - $-infinity in.not E and +infinity in.not E$，那么即为实数上的上下确界，前面业已证明
  + $M in RR^*$，是$E$的一个上界，那么$sup(E) <= M$
    - $+infinity in E$，由于$M$是$E$的上界，那么$M = +infinity$，同时$sup(E) = +infinity = M$
    - $E subset.eq RR$，那么如实数中，上界总大于等于上确界
    - $+infinity in.not E and -infinity in E$，那么$sup(E) = sup(E without {-infinity}) in RR$，如实数中的情况
  + $M in RR^*$，是$E$的一个下界，那么$inf(E) <= M$
    - $-infinity in E$，那么$M = -infinity$，于是$inf(E) = -infinity = M$
    - $E subset.eq RR$，那么如实数中，下界总大于等于下确界
    - $-infinity in.not E and +infinity in E$，那么$+infinity in.not -E and -infinity in -E$，那么$inf(E) = -sup(-E) = -sup(-E without {-infinity}) in RR$，如实数中的情况
]

== 序列的上确界和下确界

#definition[序列的上确界和下确界][

  $(a_n)_(n=m)^infinity$是实数序列，定义：

  + 序列的上确界为$ sup((a_n)_(n=m)^infinity) := sup{a_n:n>=m} $
  + 序列的下确界为$ inf((a_n)_(n=m)^infinity) := inf{a_n:n>=m} $

  有时也记作
  $
    sup((a_n)_(n=m)^infinity) = sup_(n>=m)a_n\
    inf((a_n)_(n=m)^infinity) = inf_(n>=m)a_n
  $
]

#property[最小上界性质][
  $(a_n)_(n=m)^infinity$是实数序列，$x = sup(a_n)_(n=m)^infinity in RR^*$，那么

  + $forall n >=m, a_n <= x$
  + $M in RR^*$，是序列的一个上界，那么有$x <= M$
  + $forall y in RR^*, y < x => exists n >= m, y< a_n <= x$
]<prop:least-upper-bound-property>

#property[最大下界性质][
  $(a_n)_(n=m)^infinity$是实数序列，$x = inf(a_n)_(n=m)^infinity in RR^*$，那么

  + $forall n >=m, a_n >= x$
  + $M in RR^*$，是序列的一个下界，那么有$x >= M$
  + $forall y in RR^*, y > x => exists n >= m, y > a_n >= x$

]<prop:greatest-lower-bound-property>

#tip-block[
  刚好和最小上界性质反过来
]

#lemma[单调有界序列必然收敛][
  $(a_n)_(n=m)^infinity$是实数序列，$M in RR$是该序列的上界，并且该序列递增，那么该序列收敛，并且有
  $
    lim_(n->infinity)(a_n) = sup_(n>=m) a_n <= M
  $

  类似的，$M in RR$是该序列的下界，并且该序列递减，那么该序列收敛，并且有
  $
    lim_(n->infinity)(a_n) = inf_(n>=m) a_n >= M
  $
]

#note-block[
  结合之前证明：收敛序列一定有界，那么单调收敛序列一定有界；还有单调有界序列必然收敛，那么可以得到对于单调序列收敛必有界，有界必收敛
]


#problem[验证序列$(1/n)_(n=1)^infinity$的上确界是$1$，下确界是$0$]
#solution[
  + $sup_(n>=1)1/n = 1$

    易有$forall n >= 1, 1 >= 1/n > 0$，所以$1$是一个上界，令最小上界为$1 - epsilon, epsilon in RR$，由于是最小下界，那么$1 - epsilon <= 1 => epsilon >= 0$
    - 那么取$epsilon >0, 1 - epsilon < 1$
      - 如果$1 - epsilon < 0$，那么显然不是一个上界
      - 如果$0 < 1 - epsilon < 1$，那么由阿基米德性质$exists N in ZZ^+, 1/n > 1 -epsilon$，其中$1/n$也是序列中的元素，所以$1 - epsilon$不是一个上界
    - 综上，只能是$epsilon = 0$，进而最小上界为$1 - epsilon = 1$

  + $inf_(n>=1)1/n = 0$

    $forall n in ZZ^+, 1 >= 1/n > 0$，所以$0$是一个下界，现在假设最大下界为$0 + epsilon = epsilon$，由于是最大下界，那么$epsilon >= 0$

    $epsilon > 0$时，由阿基米德性质，$exists n in ZZ^+, 1/n < epsilon$，其中$1/n$是序列中的一个元素，所以$epsilon$不是一个下界

    那么只能是$epsilon = 0$，于是最大下界为$0 + epsilon = epsilon = 0$
]

#problem[证明@prop:least-upper-bound-property]
#proof[

  $(a_n)_(n=m)^infinity$是实数序列，$x = sup(a_n)_(n=m)^infinity in RR^*$

  + 由@prop:extended-real-sup-inf-properties 可证
  + 由@prop:extended-real-sup-inf-properties 可证
  + $forall y in RR^*, y < x => exists n >= m, y < a_n <=x$

    由于$x$是最小上界，那么有$a_n <= x$，由于$y < x$，那么$y != +infinity$，如果$y = -infinity$，那么一定有$y < a_n <= x$，因为$(a_n)_(n=m)^infinity$是实数序列

    如果$y in RR$，定义集合$E := {a_n : n>= m}$，所以$x = sup_(n>=m)a_n = sup(E)$

    假设$forall n >= m, y >= a_n$，这意味这$y$是$E$的一个上界，由于$x$是最小上界，于是$y >= x$，这与$y < x$矛盾，所以$exists n >=m, y < a_n <= x$
]

#problem[单调有界序列必然收敛][
  $(a_n)_(n=m)^infinity$是实数序列，$M in RR$是该序列的上界，并且该序列递增，那么该序列收敛
]
#proof[
  由于$M in RR$是该序列的一个上界，那么上确界有一定是实数，所以令$x = sup_(n>=m)a_n in RR$，那么任取$epsilon in RR^+$，就有$x - epsilon < x$，于是$ exists N >= m, x-epsilon < a_N <= x $由于该序列单调递增，那么$forall n >= N, a_n >= a_N$，于是有
  $ x - epsilon & < a_N <= a_n <= x < x + epsilon \
              & => -epsilon < a_n - x < epsilon \
              & => abs(a_n - x) < epsilon $这正是序列收敛的定义，于是就有
  $
    lim_(n->infinity)a_n = sup_(n>=m)a_n <= M
  $
]

#problem[证明$x > 1$时，$(x^n)_(n=1)^infinity$不收敛]
#proof[
  定义新序列$(1/x^n)_(n=1)^infinity$，由于$x > 1$，那么$ forall n,m in ZZ^+, n>=m => x^n > x^m > 1 => 0 < 1/x^n <1/x^m < 1 $于是$(1/x^n)_(n=1)^infinity$是单调递减的，且有$inf_(n>=m)1/x^n = 0$，于是$ lim_(n->infinity)1/x^n = 0 $

  现在假设$(x^n)_(n=1)^infinity$收敛到$L$，同时根据$1/x^n x^n = 1$，就有$0 L = 0 = 1$，矛盾，所以$x > 1$时，$(x^n)_(n=1)^infinity$不收敛
]

== 上极限、下极限和极限点

#definition[极限点][
  $x in RR, epsilon in RR^+, (a_n)_(n=m)^infinity$是实数序列，定义：
  + $x$是$epsilon$-贴附于$(a_n)_(n=m)^infinity$的$<=>$存在一个$n>= m$，使得$a_n$可以$epsilon$-接近于$x$
  + $x$是持续$epsilon$-贴附于$(a_n)_(n=m)^infinity$的$<=> forall N >= m, (a_n)_(n=N)^infinity$是$epsilon$-贴附于$x$的
  + $x$是$(a_n)_(n=m)^infinity$的极限点/黏附点$<=> forall epsilon in RR^+$，$x$是持续$epsilon$-贴附于$(a_n)_(n=m)^infinity$的

  将上述定义展开就有，如果$x$是序列$(a_n)_(n=m)^infinity$的极限点，那么就有
  $
    forall epsilon in RR^+, forall N >= m, exists n>= N, abs(a_n - x) <= epsilon
  $
]
#remark[
  观察定义(2)的描述，其实相当于抛弃了前$N-m$项，然后在剩下的序列元素中研究
]

#lemma[极限其实也是极限点][
  实数序列$(a_n)_(n=m)^infinity$收敛到$L$，那么$L$也是该序列的极限点，且是唯一的极限点
]<lem:limit-is-unique-limit-point>
#proof[
  任取$epsilon in RR^+, N >= m$，由收敛定义有
  $ exists N_0 >= m, forall n >= N_0, abs(a_n - x) <= epsilon $现在取$n = max(N, N_0)$，那么有$n >= N_0 and n>=N$，所以有$ abs(a_n-L) <= L $也即
  $ forall N >= m, exists n >= N, abs(a_n - L) <= epsilon $所以$L$是该序列的一个极限点

  收敛序列的极限点唯一可由收敛的唯一性直接得到
]

#definition[上极限和下极限][

  $(a_n)_(n=m)^infinity$是序列，现在定义序列$(a_N^+)_(N=m)^infinity$，其中
  $
    a_N^+ := sup(a_n)_(n = N)^infinity
  $

  定义_序列$(a_n)_(n=m)^infinity$的上极限_为
  $ lim_(n->infinity) sup a_n := inf(a_N^+)_(N = m)^infinity $

  类似的，定义序列$(a_N^-)_(N=m)^infinity$，其中
  $ a_N^- := inf(a_n)_(n=N)^infinity $
  并定义_序列$(a_n)_(n=m)^infinity$的下极限_为
  $
    lim_(n->infinity)inf a_n := sup(a_N^-)_(N = m)^infinity
  $
  // 有时也将上下极限记作
  // $
  //   lim_(n->infinity)sup a_n = overline(lim)_(n->infinity)a_n\
  //   lim_(n->infinity)inf a_n = underline(lim)_(n->infinity)a_n\
  // $
]

#note-block[
  $a_N^+$相当于将原序列从$a_N$处截断，取包含$a_N$的尾部的上确界，若干个这样的上确界组成了一个新序列，取新序列的下确界，即为上极限
]

#property[序列上/下极限点的性质][
  $(a_n)_(n=m)^infinity$是一个实数序列，$L^+, L^- in RR^*$是该序列的上/下极限点，有下列成立

  + $forall x > L^+, exists N >= m, forall n >= N, a_n < x$
  + $forall y < L^-, exists N >= m, forall n >= N, a_n > y$
  + $forall x < L^+, forall N >= m, exists n >= N, a_n > x$
  + $forall y > L^-, forall N >= m, exists n >= N, a_n < y$
  + $inf(a_n)_(n=m)^infinity <= L^- <= L^+ <= sup(a_n)_(n=m)^infinity$
  + $c$是序列$(a_n)_(n=m)^infinity$的任意极限点，那么$L^- <= c <= L^+$
  + $L^+$是有限的，那么$L^+$是序列的一个极限点
  + $L^-$是有限的，那么$L^-$是序列的一个极限点
  + $c in RR, lim_(n->infinity)a_n = c <=> L^+ = L^- = c$
]<prop:sequence-limit-point-properties>

#lemma[比较引理][
  $(a_n)_(n=m)^infinity,(b_n)_(n=m)^infinity$是两个实数序列，满足$forall n >= m, a_n <= b_n$，那么有如下不等式成立
  + $ sup(a_n)_(n=m)^infinity <= sup(b_n)_(n=m)^infinity $
  + $ inf(a_n)_(n=m)^infinity <= inf(b_n)_(n=m)^infinity $
  + $ lim_(n->infinity) sup a_n <= lim_(n->infinity) sup b_n $
  + $ lim_(n->infinity) inf a_n <= lim_(n->infinity) inf b_n $
]<lem:comparison-lemma>

#corollary[夹逼检验][
  $(a_n)_(n=m)^infinity, (b_n)_(n=m)^infinity, (c_n)_(n=m)^infinity$是实数序列，满足
  $
    forall n >= m, a_n <= b_n <= c_n
  $
  如果$(a_n)_(n=m)^infinity, (c_n)_(n=m)^infinity$都收敛到$L$，那么$(b_n)_(n=m)^infinity$也收敛到$L$
]<cor:squeeze-test>

#corollary[数列零检验][
  实数序列$(a_n)_(n=m)^infinity$的极限存在且等于$0$，当且仅当极限$lim_(n->infinity)abs(a_n)$存在且等于$0$
]<cor:zero-limit-test>

#theorem[实数的完备性][
  实数序列$(a_n)_(n=m)^infinity$是柯西序列，当且仅当它是收敛的
]<thm:completeness-of-real-numbers>
#proof[
  - $=>$\
    $(a_n)_(n=m)^infinity$是柯西序列，那么它是有界的，所以由@prop:sequence-limit-point-properties(5)可得$L^+,L^- in RR$

    利用柯西序列的定义就有
    $
      forall epsilon/2 in RR^+, exists N >= 1, forall n >= N, abs(a_n - a_N) <= epsilon/2 => -epsilon/2 + a_N <= a_n <= epsilon/2 + a_N
    $
    由@lem:comparison-lemma 就有
    $ -epsilon/2 + a_N <= inf(a_n)_(n=N)^infinity <= sup(a_n)_(n=N)^infinity <= epsilon/2 + a_N $再次利用@lem:comparison-lemma 搭配上下极限定义，就有
    $ & -epsilon/2 + a_N <= L^- <=L^+ <= epsilon/2 + a_N \
    & => 0<=L^+ - L^-<= epsilon => abs(L^+ - L^-) <= epsilon $由于$epsilon$是任取的，那么$L^+ = L^-$，结合@prop:sequence-limit-point-properties(9)，说明$(a_n)_(n=1)^infinity$是收敛的

  - $arrow.double.l$ 见@lem:convergent-implies-cauchy 的证明
]

#definition[没有有限上下界][
  对于序列$(a_n)_(n=m)^infinity$，其极限点为$c$
  - $c = +infinity <=>$该序列没有有限上界
  - $c = -infinity <=>$该序列没有有限下界
]


#problem[证明 @lem:limit-is-unique-limit-point]
#proof[见 @lem:limit-is-unique-limit-point 的证明]

#problem[证明极限点/上极限/下极限的定义中，起始角标的选取是无关紧要的][
  + $(a_n)_(n=m)^infinity$是实数序列，$m >= m'$，那么$c$是$(a_n)_(n=m)^infinity$的极限点，当且仅当$c$是$(a_n)_(n=m')^infinity$的极限点
  + $(a_n)_(n=m)^infinity$和$(a_(n+k))_(n=m)^infinity$是两个实数序列，且$k >= 0$，那么$c$是$(a_n)_(n=m)^infinity$的极限点，当且仅当$c$是$(a_(n+k))_(n=m)^infinity$的极限点
  + $(a_n)_(n=m)^infinity$是实数序列，$m <= m'$，那么$c$是$(a_n)_(n=m)^infinity$的上极限，当且仅当$c$是$(a_n)_(n=m')^infinity$的上极限
  + $(a_n)_(n=m)^infinity$是实数序列，$k >= 0$，那么$c$是$(a_(n+k))_(n=m)^infinity$的上极限，当且仅当$c$是$(a_n)_(n=m)^infinity$的上极限
  + $(a_n)_(n=m)^infinity$是实数序列，$m <= m'$，那么$c$是$(a_n)_(n=m)^infinity$的下极限，当且仅当$c$是$(a_n)_(n=m')^infinity$的下极限
  + $(a_n)_(n=m)^infinity$是实数序列，$k >= 0$，那么$c$是$(a_(n+k))_(n=m)^infinity$的下极限，当且仅当$c$是$(a_n)_(n=m)^infinity$的下极限
]
#proof[
  + 由于$c$是$(a_n)_(n=m)^infinity$的极限点，就有
    $ forall epsilon in RR^+, forall N >= m, exists n>= N, abs(a_n - c) <= epsilon $自然有$N >= m >= m'$，于是
    $ forall epsilon in RR^+, forall N >= m',exists n >= N, abs(a_n - c) <= epsilon $这说明$c$是$(a_n)_(n=m')^infinity$的极限点\ \

    由于$c$是$(a_n)_(n=m')^infinity$的极限点，那么有
    $ forall epsilon in RR^+, forall N >= m', exists n >= N, abs(a_n - c) <= epsilon $对于$(a_n)_(n=m)^infinity$取$N >= m >= m'$，于是有$ forall epsilon in RR^+, forall N >= m>=m', exists n >= N, abs(a_n - c) <= epsilon $

    #note-block[
      由于对于任意的$N >= m'$，总存在$n >= N$满足上式，就算$N$取值到了$m$到$m'$之间，$n$也可以取到后面的值，因为只要求存在一个$n >= N$满足不等式
    ]

  + 令$m' = m+k>=m$，那么$ (a_(n+k))_(n=m)^infinity=(a_n)_(n=m')^infinity $由(1)易证

  + 由上极限的定义，有
    $ lim_(n->infinity) sup a_n = inf (a_N^+)_(N = m)^infinity $
    其中$(a_N^+) = sup(a_n)_(n=N)^infinity$，所以有
    $
      a_m^+ >= a_(m-1)^+ >= ... >= a_(m')^+>= ...
    $
    所以从$m'$开始算的序列的下确界和从$m$开始算的序列的下确界是相等的，只不过后者比前者多了$a_m^+,...,a_(m'-1)^+$这些元素，而且它们单调递减，即便删除也不影响对下确界的判断

  + 令$m' = m + k >= m$，那么就有
    $
      (a_(n+k))_(n=m)^infinity = (a_n)_(n = m')^infinity
    $
    由(3)易证

  + 下极限同(3)

  + 下极限同(4)
]
#note-block[
  以上的结果说明，极限点/上下极限的判断与序列起始位置无关，与序列平移也无关
]


#problem[证明@prop:sequence-limit-point-properties ]
#proof[
  $(a_n)_(n=m)^infinity$是一个实数序列，$L^+, L^- in RR^*$是该序列的上/下极限点
  + $forall x > L^+, exists N >= m, forall n >= N, a_n < x$\
    $x > L^+$，由于$L^+ = inf(a_N^+)_(N =m)^infinity$，那么$x > inf(a_N^+)_(N =m)^infinity$，于是
    $ exists N >= m, x > a_N^+ = sup(a_n)_(n=N)^infinity $进一步就有
    $ forall n>= N, x > a_n $综上得证

  + $forall y < L^-, exists N >= m, forall n >= N, a_n > y$\
    $y < L^-$，由于$L^- = sup(a_N^-)_(N = m)^infinity$，那么$y < sup(a_N^-)_(N = m)^infinity$，于是
    $ exists N >= m, y < a_N^+ = inf(a_n)_(n=N)^infinity $进一步有
    $ forall n >= N, y < a_n $综上得证

  + $forall x < L^+, forall N >= m, exists n >= N, a_n > x$\
    $x < L^+$，由于$L^+ = inf(a_N^+)_(N = m)^infinity$，那么$x < inf(a_N^+)_(N = m)^infinity$，于是
    $ forall N >= m, x < a_N^+ = sup(a_n)_(n=N)^infinity $进一步有
    $ exists n >= N, x < a_n $综上得证

  + $forall y > L^-, forall N >= m, exists n >= N, a_n < y$\
    $y > L^-$，由于$L^- = sup(a_N^-)_(N = m)^infinity$，$y > sup(a_N^-)_(N = m)^infinity$，于是
    $ forall N >= m, y > a_N^- = inf(a_n)_(n=N)^infinity $进一步有
    $ exists n >= N, y > a_n $综上得证

  + $inf(a_n)_(n=m)^infinity <= L^- <= L^+ <= sup(a_n)_(n=m)^infinity$\

    $L^+ = inf(a_N^+)_(N=m)^infinity$，定义集合$E = {sup(a_n)_(n=N)^infinity:N>=m }$，于是$sup(a_n)_(n=m)^infinity in E$，由于$L^+ = inf(E)$，那么就有$L^+ <= sup(a_n)_(n=m)^infinity$

    同理，就有$inf(a_n)_(n=m)^infinity <= L^-$

    假设$L^- > L^+$，所以
    $ exists N >= m, sup(a_N^-)_(N=m)^infinity > a_N^+\ $进而有
    $ exists M >= m, a_N^+ < a_M^- <=sup(a_N^-)_(N=m)^infinity $取$p = N + M + 1$，那么$p > N, p > M$，于是就有$a_p < a_N^+ < a_M^- < a_p => a_p < a_p$，矛盾

    综上$inf(a_n)_(n=m)^infinity <= L^- <= L^+ <= sup(a_n)_(n=m)^infinity$

  + $c$是序列$(a_n)_(n=m)^infinity$的任意极限点，那么$L^- <= c <= L^+$\
    假设$c > L^+$，那么取$epsilon = (c - L^+)/2 > 0$，由于$c$是极限点，那么就有
    $ forall N >= m, exists n >= N, abs(a_n - c) <= epsilon\
    => a_n >= -epsilon + c =( L^+ + c )/2 > L^+ $因为任意的$N>=m$都存在$n >= N$满足上式，说明序列$(a_n)_(n=N)^infinity$至少有一项大于$( L^+ + c )/2$，所以有
    $ a_N^+ = sup(a_n)_(n=N)^infinity >= ( L^+ + c )/2 $可以看到序列$(a_N^+)_(N=m)^infinity$中的每一项都满足大于等于$( L^+ + c )/2$，所以就有
    $ L^+ = inf(a_N^+)_(N=m)^infinity >= (L^+ + c)/2 => c <= L^+ $与假设矛盾，所以$c <= L^+$

    假设$L^- > c$，那么取$epsilon = (L^- - c )/ 2 > 0$，由于$c$是一个极限点，那么
    $ forall N >= m, exists n >= N, abs(a_n - c) <= epsilon\
    => a_n <= epsilon + c = (L^- + c) / 2 < L^- $于是说明任意的$N >= m$，总存在$n >= N$满足上式，说明序列$(a_n)_(n=N)^infinity$至少有一项小于$(L^- + c) / 2$，所以有
    $ a_N^- = inf(a_n)_(n=N)^infinity <= (L^- + c) / 2 $可以看到序列$(a_N^-)_(N=m)^infinity$的每一项都小于等于$(L^- + c) / 2$，所以有
    $ L^- = sup(a_N^-)_(N=m)^infinity <= (L^- + c)/2 => L^- <= c $与假设矛盾，所以有$L^- <= c$

    综上$L^- <= c <= L^+$
  + $L^+$是有限的，那么$L^+$是序列的一个极限点\
    任取$epsilon in RR^+$，由于$L^+ in RR$，那么有
    $
      L^+ - epsilon < L^+ < L^+ + epsilon
    $
    对于前半部分，有
    $
      forall N >= m, exists n >= N, L^+ - epsilon < a_n
    $
    对于后半部分，有
    $ exists N' >= m, forall n >= N', a_n < L^+ + epsilon $取$N'' = max(N, N')$于是有
    $ forall N'' >= m ,exists n >= N'', L^+ - epsilon< a_n < L^+ + epsilon => abs(a_n - L^+) < epsilon $这说明$L^+$是一个极限点

  + $L^-$是有限的，那么$L^-$是序列的一个极限点\
    任取$epsilon in RR^+$，由于$L^- in RR$，那么
    $
      L^- - epsilon < L^- < L^- + epsilon
    $
    对于前半部分，有
    $
      exists N' >=m, forall n >= N, a_n > L^- - epsilon
    $
    对于后半部分，有
    $
      forall N >= m, exists n >= N', a_n < L^- + epsilon
    $
    取$N'' = max(N, N')$，就有
    $ forall N'' >= m, exists n >= N'', L^- - epsilon < a_n < L^- + epsilon => abs(a_n - L^-) < epsilon $这说明$L^-$是一个极限点
  + $c in RR, lim_(n->infinity)a_n = c <=> L^+ = L^- = c$\
    - $=>$\
      由于极限也是极限点，那么由(6)就有
      $ L^- <= c <= L^+ $由于序列收敛到$c$，那么就有
      $
        forall epsilon in RR^+, exists N >= m, forall n >= N, abs(a_n - c) <= epsilon => -epsilon + c <= a_n <= epsilon + c
      $
      于是就有
      $ forall n >= N, a_n <= epsilon + c => a_N^+ = sup(a_n)_(n=N)^infinity <= epsilon + c\
      forall n >= N, a_n >= -epsilon + c => a_N^- = inf(a_n)_(n=N)^infinity >= -epsilon + c $进而有
      $ L^+ = inf(a_k^+)_(k = N)^infinity <= epsilon + c\
      L^- = sup(a_k^-)_(k = N)^infinity >= -epsilon + c\ $所以就有
      $ -epsilon + c <= L^- <= L^+ <= epsilon + c\
      => abs(L^+ - c) <= epsilon, abs(L^- - c) <= epsilon $由于$epsilon$是任取的，就有$L^+ = L^- = c$
    - $arrow.double.l$\
      任选$epsilon in RR^+$，由(5)可得
      $
        -epsilon + c = -epsilon + L^- < L^- = L^+ < epsilon + L^+ = epsilon + c
      $
      对于前半部分有
      $
        exists N >=m, forall n >= N, a_n > -epsilon + c
      $
      对于后半部分有
      $
        exists N' >= m, forall n >= N', a_n < epsilon + c
      $
      取$N'' = max(N, N')$，于是有
      $ forall n >= N'',-epsilon + c < a_n < epsilon + c => abs(a_n - c) < epsilon $于是序列收敛到$c$
]

#problem[证明@lem:comparison-lemma]
#proof[
  $(a_n)_(n=m)^infinity,(b_n)_(n=m)^infinity$是两个实数序列，满足$forall n >= m, a_n <= b_n$
  + $sup(a_n)_(n=m)^infinity <= sup(b_n)_(n=m)^infinity$\
    $
      & forall n>=m, a_n <= b_n \
      & => a_n <= b_n <= sup(b_n)_(n=m)^infinity \
      & => sup(a_n)_(n=m)^infinity <= sup(b_n)_(n=m)^infinity
    $
  + $inf(a_n)_(n=m)^infinity <= inf(b_n)_(n=m)^infinity$\
    $
      & forall n >= m, a_n <= b_n \
      & => inf(a_n)_(n=m)^infinity <= a_n <= b_n \
      & => inf(a_n)_(n=m)^infinity <= inf(a_n)_(n=m)^infinity
    $
  + $lim_(n->infinity) sup a_n <= lim_(n->infinity) sup b_n$\
    $
      & forall N >= m,forall n >= N >=m, a_n <= b_n =>sup(a_n)_(n=N)^infinity <= sup(b_n)_(n=N)^infinity \
      & => forall N >=m, a_N^+ <= b_N^+ \
      & => inf(a_N^+)_(N=m)^infinity <= inf(b_N^+)_(N=m)^infinity \
      & => lim_(n->infinity) sup a_n <= lim_(n->infinity) sup b_n
    $
  + $lim_(n->infinity) inf a_n <= lim_(n->infinity) inf b_n$\
    同(3)的证明
]

#problem[证明@cor:squeeze-test]
#proof[
  由于$(a_n)_(n=m)^infinity, (c_n)_(n=m)^infinity$都收敛到$L$，那么就有
  $
    lim_(n->infinity) sup a_n = lim_(n->infinity) inf a_n = L\
    lim_(n->infinity) sup c_n = lim_(n->infinity) inf c_n = L\
  $
  由于$forall n >= m, a_n <= b_n <= c_n$，那么就有
  $
    & L = lim_(n->infinity) sup a_n<=lim_(n->infinity) sup b_n <= lim_(n->infinity) sup c_n = L \
    & L = lim_(n->infinity) inf a_n<=lim_(n->infinity) inf b_n <= lim_(n->infinity) inf c_n = L \
  $
  所以$lim_(n->infinity) inf b_n = lim_(n->infinity) sup b_n = L$，所以$(b_n)_(n=m)^infinity$收敛且收敛到$L$
]

#problem[构造一个例子：序列$(a_n)_(n=1)^infinity$和$(b_n)_(n=1)^infinity$，满足$forall n in ZZ^+, a_n < b_n$，但是$sup(a_n)_(n=1)^infinity lt.not sup(b_n)_(n=1)^infinity$]
#solution[

  取$a_n = 1 - 1/n, b_n = 1$，所以$forall n in ZZ^+, a_n = 1- 1/n < 1 = b_n$

  易知$sup(b_n)_(n=m)^infinity = sup(a_n)_(n=m)^infinity = 1$，所以$sup(a_n)_(n=m)^infinity lt.not sup(b_n)_(n=m)^infinity$

  // @lem:comparison-lemma 中要求$<=$而非$<$，所以不冲突
]

#problem[证明@cor:zero-limit-test]
#proof[
  - $=>$\
    $lim_(n->infinity)a_n=0$说明
    $ forall epsilon in RR^+, exists N >= m, forall n >= N, abs(a_n - 0) = abs(a_n) = abs(abs(a_n)) <= epsilon $这正是序列$(abs(a_n))_(n=m)^infinity$收敛到$0$的定义

  - $arrow.double.l$\
    $lim_(n->infinity)abs(a_n)=0$说明
    $ forall epsilon in RR^+, exists N >=m, forall n>=N,abs(abs(a_n) - 0) = abs(abs(a_n))= abs(a_n) = abs(a_n - 0) <= epsilon $这正是序列$(a_n)_(n=m)^infinity$收敛到$0$的定义
]

#problem[$c != 0, lim_(n->infinity)a_n = c <=> lim_(n->infinity)abs(a_n) = c$，是否还正确？]
#proof[
  - $c < 0$时显然不正确，例如$lim_(n->infinity)(-1) = -1$，$lim_(n->infinity)(abs(-1)) = 1$
  - $c > 0$时
    - $=>$\
      取$epsilon = c/2 > 0$，那么
      $ exists N >= m, forall n >= N, abs(a_n - c) <= c/2 => 0 < c/2 <= a_n <= (3c)/2 $所以$n >= N$时$abs(a_n) = a_n$，于是$lim_(n->infinity)abs(a_n) = c$
    - $arrow.double.l$\
      取$a_n = -1$，那么$abs(a_n) = 1$，于是$lim_(n->infinity)abs(a_n) = 1, lim_(n->infinity)a_n = -1$，二者不相等

  综上当$c > 0$时，$lim_(n->infinity)a_n = c => lim_(n->infinity)abs(a_n) = c$
]

#problem[证明$lim_(n->infinity)sup a_n$是序列$(a_n)_(n=m)^infinity$的一个极限点，而且是最大的极限点]
#proof[
  令$lim_(n->infinity)sup a_n = L$\
  - 如果$L in RR$，那么由@prop:sequence-limit-point-properties(7)，$L$是一个极限点，由@prop:sequence-limit-point-properties(6)，$L$大于任意极限点，所以$L$是最大极限点
  - 如果$L = +infinity$，对任意极限点$c$都有$+infinity >= c$，所以$L$是最大极限点
]

#problem[构造一个序列$(a_n)_(n=1)^infinity$，只有三个极限点$-infinity, 0, +infinity$]
#proof[
  定义序列
  $ a_n = cases(n&\,n=3q, -n&\,n=3q+1, 0&\,n=3q+2) $其中$q in NN$
]

#problem[$(a_n)_(n=N)^infinity$和$(b_m)_(m=M)^infinity$是实数序列，且满足$forall m >= M, b_m$是$(a_n)_(n=N)^infinity$的极限点，令$c$是$(b_m)_(m=M)^infinity$的极限点，证明$c$也是$(a_n)_(n=N)^infinity$的极限点]
#proof[
  由于$c$是$(b_m)_(m=M)^infinity$的极限点，那么
  $ forall epsilon/2 in RR^+, forall K >= M, exists m >= K, abs(b_m - c) <= epsilon/2 $由于$b_m$是$(a_n)_(n=N)^infinity$的极限点，那么
  $ forall epsilon/2 in RR^+, forall K' >= M, exists n >= K'm abs(a_n - b_m) <= epsilon $取$K'' = max(K, K')$就有
  $ forall K'' >= max(N, M), exists n >= K'', abs(a_n - c) <= abs(a_n - b_m) + abs(b_m - c) <= epsilon/2 + epsilon/2 = epsilon $于是$c$也是$(a_n)_(n=N)^infinity$的一个极限点
]

== 一些常用的极限


#pagebreak()
