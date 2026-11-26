#import "@preview/theorion:0.6.0": *
#import cosmos.fancy: *

= 无限集

== 可数性

#definition[可数集合][
    + 集合$X$被称作可数无穷的（或可数的），当且仅当$X$与$NN$有相同的基数
    + 集合$X$被称作是至多可数的，当且仅当$X$是可数的或有限的
    + 集合$X$被称作是不可数的，当且仅当$X$既不可数、也不有限
]

#proposition[良序原理][
    $X$是$NN$的非空子集，那么唯一存在$n in X$，满足$forall m in X, n <= m$
]<proposition:well-ordering-principle>
#proof[
    对$X$的基数进行归纳，由于$X$非空，当$\#(X) = 1$时，有$X = {x}, x in NN$，显然有$x <= x$.

    现在归纳性的假设$\#(X) = n$时成立，证明$\#(X) = n+1$的情况，令$X' subset.eq NN and \#(X') = n, X = X' union {x_0}, x_0 in.not X'$

    根据归纳假设唯一存在$n in X', forall m in X', n <= m$，那么对于$X$来说

    - 如果$x_0 <= n$，那么$forall m in X, x_0 <= n <= m$
    - 如果$x_0 > n$，那么$forall m in X, n <= m$
    - 由自然数的三歧性，考虑的所有情况都成立，归纳结束

    于是自然数的非空子集有最小值，记作$min(X)$
]

#proposition[
    $X$是$NN$的无穷子集，那么存在唯一双射$f: NN->X$，且是单调递增的；特别的，$X$与$NN$有相同的基数，因此$X$是可数的
]<proposition:for-X-NN-conuntbale>
#proof[
    定义一个自然数序列$(a_n)_(n=0)^oo$，每一项如下
    $
        a_n := min{x in X: x != a_m forall m < n}
    $
    直觉上来说，这个定义将$X$进行升序排序，并用自然数$n$去索引每一个$X$中的元素，比如$n = 0$时，由于没有自然数小于$0$，所以上式即为
    $
        a_0 = min{x in X}
    $也即选出了$X$中的最小元素，并绑定到$a_0$上

    当$n = 1$时，上式即为
    $
        a_1 = min{x in X: x != a_m forall m < 1} = min{x in X: x!= a_0} = min(X without {a_0})
    $也即选出了$X$中第$2$小的元素，并绑定到$a_1$上

    由@proposition:well-ordering-principle 可知，要取自然数子集的最小值就要求该子集是非空的，这里证明集合$S_n = {x in X: x!=a_m forall m < n}$是无穷的，假设$S_n$是有限的，那么就有
    $
        X = S_n union {a_m: forall m< n}
    $${a_m : forall m < n}$是有限集合，根据假设$S_n$也是有限集合，所以$X$也是有限集合，这与$X$是无穷集合的条件矛盾，所以$S_n$是无穷集合，进而$S_n$是非空的，所以$a_n$是良定义的.

    接下来证明序列$(a_n)_(n=0)^oo$是单调递增的，也即$a_n < a_(n+1), forall n in NN$成立，对$n$归纳，当$n = 0$时
    $
        a_0 = min(X), a_1 = min(X without {a_0})
    $假设$a_0 >= a_1$，由$a_n$的定义，总有$a_m != a_n, forall m!=n$，此外可以得到$a_1 = min(X)$，这说明存在两个不同的自然数都是该子集的最小值，与@proposition:well-ordering-principle 矛盾，所以$a_0 < a_1$

    归纳性的假设$n$时成立，现在证明$n+1$的情况
    $
        a_(n+2) = min{x in X: x != a_m, forall m < n+2} = min(X without {a_m: forall m < n+2})
    $类似与$n=0$时的讨论，就有$a_(n+1) < a_(n+2)$，归纳结束

    定义函数$f: NN -> X, f(n) = a_n$，由上可知，$f$单调递增，因为$a_m!=a_n, forall m !=n$，所以$f$是单射.

    接下来证明$f$是满射，任取$x in X$，假设任意$n in NN$，都有$x != a_n$，这意味这$forall n in NN, x in {x in X: x!= a_m, forall m < n}$，由$a_n$定义，就有$forall n in NN, x > a_n$.

    接下来需要证明一个额外的引理：$(a_n)_(n=0)^oo$是严格单调递增自然数序列，那么总有$a_n >= n$成立，对$n$进行归纳，$n=0$时，$a_0 >= 0$总成立，因为任意自然数都大于等于$0$，归纳性的假设$n$时成立，那么就有$a_n >= n$，现在证明$n+1$的情况，由于$(a_n)_(n=0)^oo$单调递增，所以就有
    $
        a_(n+1) > a_n >= n => a_(n+1) >= n+1
    $成立，归纳结束

    回到原命题，就有$forall n in NN, x>a_n >= n$，这意味这$x$比任何自然数都大，矛盾，所以对于每个$x in X$，存在$n in NN$，使得$f(n) = x$，所以$f$是满射.
    结合之间的结果，$f$是双射

    现在证明这样的$f$是唯一的，假设还有另一个函数$g:NN->X$也满足条件，但是$f!=g$，那么集合${n in NN: f(n) != g(n)}$是非空的，定义$m := min(n in NN: g(n) != f(n))$，于是就有$g(m) != f(m) = a_m$，对于任意小于$m$的$n$来说，都有$n != m$，进而$g(n) = f(n) = a_n$，于是就有
    $
        & g(0) = f(0) = a_0 \
        & ... \
        & g(m-1) = f(m-1) = a_(m-1) \
        & g(m) != f(m) = a_m
    $定义集合$S_m = {x in X: x != a_t, forall t < m}$，由于$forall t < m, g(t) = a_t$且$g$单调递增，那么
    $
        forall t < m , a_t = g(t) < g(m) => g(m) in S_m
    $由于$a_m = min(S_m)$，那么$g(m) >= a_m$，假设$g(m) > a_m$，由于$g$是满射，那么存在$k$使得$g(k) = a_m$
    - 如果$k > m$，由于$g$是单调递增的，那么$a_m = g(k) > g(m)$，矛盾
    - 如果$k = m$，那么$g(m) = a_m$，矛盾
    - 如果$k < m$，那么$g(k) = a_k != a_m$，矛盾
    综上，无法找到$k$满足$g(k) = a_m$，进而$g(m) > a_m$不成立，只能是$g(m) = a_m$但这与$g(m) != f(m) = a_m$矛盾，所以这样的函数$f$是唯一的

    于是，自然数的无穷子集与自然数集有相同的基数
]

#corollary[自然数的子集都是至多可数的]<coro:subset-of-NN-countable>
#corollary[$X$是一个至多可数集合，$Y subset.eq X$，那么$Y$也是至多可数的]<coro:subset-of-countable-set-countable>
#proof[
    $X$是有限集合时，显然成立

    $X$是可数集合时，有双射$f:X->NN$，由于$Y subset.eq X$，那么限制$f$为$f':Y->f(Y)$，易知$f'$也是一个双射，所以$Y$与$f(Y)$有相同的基数，由于$f(Y) subset.eq NN$，根据@coro:subset-of-NN-countable 可知$f(Y)$也是可数的，进而$Y$也是可数的
]

#proposition[$Y$是一个集合，$f:NN->Y$是函数，那么$f(NN)$是至多可数的]<proposition:f-NN-countable>
#proof[
    定义集合
    $
        A := {n in NN : f(m) != f(n), forall 0<=m<n}
    $限制$f$为$f': A->f(A)$，首先确定$f(A)$和目标$f(NN)$的关系，由于$A subset.eq NN$，那么$f(A) subset.eq f(NN)$显然成立.

    接下来需要证明$f(NN) subset.eq f(A)$，也即$forall y in f(NN), y in f(A)$.
    任选$n in NN$，定义集合
    $
        E_n := {k in NN: f(k) = f(n)}
    $显然$E_n$是$NN$的子集，且至少包含元素$n$，于是由@proposition:well-ordering-principle 就有$n_0 = min(E)$，那么$f(n_0) = f(n)$，接下来证明$n_0 in A$，那么要求$forall 0<=m<n_0, f(m) != f(n_0)$，假设存在$0 <= m' < n_0$满足$f(m') = f(n_0)$，于是就有
    $
        f(m') = f(n_0) = f(n) => m' in E_n
    $但是$m' < n_0 = min(E_n)$，这与@proposition:well-ordering-principle 矛盾，所以不存在这样的$m'$，进而$n_0 in A$，由于$n$是任取的，就有$forall f(n) in f(NN), f(n) = f(n_0) in f(A)$，于是就有$f(NN) subset.eq f(A)$，综上$f(A) = f(NN)$

    为了证明$f(NN)$是至多可数的，只需证明$f(A)$是至多可数的，进而需要证明$f'$是双射，首先是单射，任取$n_1, n_2 in A$，（这里已经指定了$n_1,n_2$来自$A$，所以函数就写为了$f$而非$f'$）假设$f(n_1) = f(n_2)$
    - 如果$n_1 < n_2$，根据$A$的定义，就有$f(n_1) != f(n_2)$，矛盾
    - 如果$n_1 > n_2$，根据$A$的定义，就有$f(n_2) != f(n_1)$，矛盾
    - 于是由自然数的三歧性，只能是$n_1 = n_2$，于是$f'$是单射

    接下来证明是满射，由于$f(A) = {f(n): forall n in A}$，显然是满射.

    于是$f$在$A$上的限制是双射，所以$f(A)$与$A$有相同的基数，同时$f(NN)$与$f(A)$有相同的基数，所以$f(NN)$与$A$有相同的基数，由于$A$是自然数的子集，由@coro:subset-of-NN-countable 可知$A$是至多可数的，进而$f(NN)$也是至多可数的
]

#corollary[
    $X$是一个可数集合，$f:X->Y$是一个函数，那么$f(X)$也是至多可数的
]<coro:countable-X-f-countable>
#proof[
    由于$X$是可数的，那么存在双射$g: NN->X$，于是$X = g(NN)$，于是就有
    $
        f compose g : NN->Y
    $所以$(f compose g)(NN) = {f(g(n)) : forall n in NN} = {f(x): forall x in X} = f(X)$，由@proposition:f-NN-countable 可知$(f compose g)(NN)$是至多可数，进而$f(X)$也是至多可数的
]

#proposition[
    $X, Y$都是可数集，那么$X union Y$是可数集
]<proposition:countable-union-contable>
#proof[
    由于都是可数集合，那么都有分别有双射$f: NN->X$和$g:NN ->Y$，接着定义函数$h: NN -> X union Y$，满足
    $
        & h(2n) = f(n) \
        & h(2n+1) = g(n)
    $接下来只需证明$h(NN) = X union Y$即可.

    $forall n in NN, h(n) in h(NN)$，当$n = 2k, k in NN$时，$h(n) in X$，当$n = 2k+1, k in NN$时，$h(n) in Y$，所以$forall h(n) in h(NN), h(n) in X union Y$，所以$h(NN) subset.eq X union Y$

    $forall a in X union Y => a in X or a in Y$，如果$a in X$，那么$exists n in NN$满足$a = f(n) = h(2n) in h(NN)$，如果$a in Y$，那么$exists n in NN, a = g(n) = h(2n+1) in h(NN)$，于是$forall a in X union Y, a in h(NN)$，所以$X union Y subset.eq h(NN)$

    综上$X union Y = h(NN)$，由@proposition:f-NN-countable 可知$h(NN)$是至多可数的，进而$X union Y$也是至多可数的

    此外，由于$X subset.eq X union Y$且$X$是无穷集合，那么$X union Y$也是无穷集合，综上可知$X union Y$是可数的
]

#note-block[
    综上可以看到，$NN$的子集和像都是至多可数的，可数集的有限并集也是可数的
]

#corollary[$ZZ$是可数的]<coro:ZZ-countable>
#proof[
    定义集合$-NN := {-n: n in NN}$，有双射$f:NN->-NN, f(n) = -n$，那么$-NN$和$NN$有相同的基数，都是可数的，而整数集$ZZ = -NN union NN$，由@proposition:countable-union-contable 可知$ZZ$也是可数的
]

#lemma[
    $A := {(n, m) in NN times NN: 0<=m<=n}$是可数的
]<lem:lem-for-countable-cartesian-products>
#proof[
    递归的定义自然数序列
    $
        & a_0 := 0 \
        & a_(n+1) := a_n + n + 1, forall n in NN
    $现在证明该序列是严格单调递增的，对$n$进行归纳，当$n=0$时，就有
    $
        a_0 = 0, a_1 = 1 => a_0 < a_1
    $成立，现在归纳性的假设$n$时成立，即$a_n < a_(n+1)$，证明$n+1$的情况
    $
        a_(n+2) = a_(n+1) + n + 2 > a_(n+1)
    $成立，归纳结束，该序列严格单调递增

    定义函数$f: A -> NN$为
    $
        f(n, m) := a_n + m
    $现在证明是$f$是单射，令$(n,m), (n', m') in A and (n, m) != (n', m')$
    - 当$n = n'$时，只能是$m != m'$，进而$a_n + m != a_n + m'$
    - 当$n' > n$时，有$n' >= n+1$，那么就有
        $
            f(n', m') = a_(n') + m' >= a_(n') >= a_(n+1) = a_n + n+ 1
        $由于$(n, m) in A$，就有$m <= n$，于是$n+1 > m$，综上就有
        $
            f(n', m') >= a_n + n + 1 > a_n + m = f(n, m)
        $所以$f(n', m') != f(n, m)$
    - 当$n' < n$时，推理同上，也能有$f(n', m') != f(n, m)$

    总之在所有情况下都有$(n, m) != (n', m') => f(n, m) != f(n', m')$成立，所以$f$是单射，那么满射函数$f: A -> f(A)$是双射，所以$A$和$f(A)$有相同的基数，由于$f(A) subset.eq NN$，那么由@coro:subset-of-NN-countable 可知$f(A)$是至多可数的，进而$A$是至多可数的

    接下来证明$A$不可能是有限的，如果$A$有限，那么$A$的子集也有限，特别的
    $
        X = {(n, 0): n in NN}
    $那么$X$是有限的，但是有双射$f:X -> NN, f((n, 0)) = n$，这说明$NN$也是有限的，矛盾，所以$A$不可能是有限的，进而$A$是可数的

]
#note-block[
    $A := {(n, m) in NN times NN: 0<=m<=n}$绘制出来是一个像三角阵的东西
]

#corollary[自然数的笛卡尔积是可数的][
    $NN times NN$是可数的
]<coro:NN-times-NN-countable>
#proof[
    由@lem:lem-for-countable-cartesian-products 可知$A = {(n, m) in NN times NN: 0<=m<=n}$是可数的，进而集合$B = {(n, m) in NN times NN: 0<=n<=m}$也是可数的，因为有双射$f:A->B, f(n, m) = (m, n)$

    同时可知$NN times NN = A union B$，所以由@proposition:countable-union-contable 可知$NN times NN$是可数的
]
#note-block[
    $A,B$是两个三角阵，互相为转置，它们的并集正好是一个正方形
]

#corollary[
    $X, Y$都是可数的，那么$X times Y$也都是可数的
]<coro:countable-cartesian-countable>
#proof[
    由于$X, Y$都是可数的，那么分别有双射函数$f: NN->X, g:NN->Y$，于是$X = f(NN), Y = g(NN)$，令$h:NN times NN -> X times Y, h(n, m) = (f(n), g(m))$，易知$h$是满射的，于是就有
    $
        h(NN times NN) = X times Y
    $根据@coro:NN-times-NN-countable 和@proposition:f-NN-countable 可知$X times Y$是至多可数的

    假设$X times Y$是有限的，那么$X times Y$的子集也是有限的，特别的
    $
        A = {(f(n), g(0)): n in NN}
    $那么说明$A$是有限的，有双射$t:NN -> A, t(n) = (f(n), g(0))$，这说明$NN$也是有限的，矛盾

    综上可数集的笛卡尔积也是可数的
]

#corollary[$QQ$是可数的]
#proof[
    由@coro:ZZ-countable 可知$ZZ$是可数的，于是$ZZ without {0}$也是可数的，进而根据@coro:countable-cartesian-countable 可知$ZZ times ZZ without {0}$也是可数的，有函数$f: ZZ times ZZ without {0} -> QQ, f(a, b) = a/b$，根据有理数的定义易有
    $
        f(ZZ times ZZ without {0}) = QQ
    $所以根据@proposition:f-NN-countable 可知$QQ$是至多可数的

    由于$NN subset.eq QQ$，所以$QQ$不可能是有限的，所以$QQ$是可数的
]

#problem[集合$X$是无穷的，当且仅当存在真子集$Y subset.neq X$和$X$有相同基数]
#proof[
    1. $arrow.l.double$\
        如果存在一个真子集$Y subset.neq X$与$X$有相同的基数，假设$X$是有限的，那么$\#(Y) < \#(X)$，这与条件矛盾，所以$X$一定是无穷的
    2. $=>$\
        由于$X$是无穷的，那么一定是非空的，先证明引理，无穷集合中包含一个可数无穷的子集，先递归的定义元素
        $
            x_0 in X, x_(n+1) in X without {x_0,...,x_n}
        $这些元素组成的集合为
        $
            S := {x_n : n in NN} subset.eq X
        $易有双射函数$h:NN->S, h(n) = x_n$，所以无穷集合中一定有一个可数无穷的子集

        接下来定义一个函数$f: X -> X without {x_0}$，易知$X without {x_0} subset.neq X$
        $
            f(x) = cases(x_(n+1)&\, x = x_n in S, x&\, x in X without S)
        $接下来证明$f$是单射，取$x, x' in X$且$f(x) = f(x')$，如果$x, x' in S$，那么存在$m,n>=1$使得$x_(m+1) = x_(n+1)$，$S$中元素互异，那么$m+1 = n+1 => x = x'$；如果$x, x' in X without S$，那么$f(x) = x = f(x') = x'$；如果$x in S, x' in X without S$，那么$f(x) in S, f(x') = x' in.not S, f(x) != f(x')$，与条件矛盾，综上$f$是单射

        然后证明$f$是满射，取$y in X without {x_0}$，如果$y in S$，那么存在$n >= 1$使得$y = x_n => y = f(x_(n-1))$，如果$y in.not S$，那么$y = f(y) = y$，综上$f$是满射，所以$f$是双射，所以存在真子集$X without {x_0}$与$X$有相同基数
]

#problem[证明@proposition:well-ordering-principle，如果命题中的自然数换为$ZZ$是否还成立，如果换为$QQ^+$是否还成立？]
#proof[
    1. 见@proposition:well-ordering-principle 的证明

    2. 如果换为$ZZ$则不成立，令$-N := {-n : n in NN}$，易知$-N$是$ZZ$的非空子集，假设存在最小元素，那么就有$a = -n = min(-N)$，于是就有
        $
            & a-1= -(n+1) in -N & a - 1 < a \
        $矛盾，所以不成立

    3. 如果换为$QQ^+$也不成立，$QQ^+$本身就是自身的非空子集，假设$a = min(QQ^+)$，那么就有
        $
            a/2 in QQ^+, a/2 < a
        $矛盾，所以不成立
]

#problem[证明@proposition:for-X-NN-conuntbale][见前]

#problem[证明@proposition:f-NN-countable][见前]

#problem[证明@coro:countable-X-f-countable][见前]

#problem[集合$A$是至多可数的，当且仅当存在单射$f:A->NN$]
#proof[
    - $=>$\
        如果$A$是至多可数的，那么$A$是有限的，或可数的，对于前者存在一个双射$f:A->{f(a): a in A}$，那么$f$自然是单射；对于后者，存在一个双射$f:A->NN$，$f$当然是一个单射
    - $arrow.l.double$\
        如果存在单射$f:A->NN$，那么$f':A-> f(A)$是双射，那么$A$和$f'(A)$有相同的基数，而$f'(A) subset.eq NN$，由@coro:subset-of-NN-countable 可知$f'(A)$是至多可数的，进而$A$是至多可数的
]

#problem[证明@proposition:countable-union-contable][见前]

#problem[证明@coro:countable-cartesian-countable][见前]

#problem[集合$I$是至多可数的，$forall alpha in I, A_(alpha)$也是至多可数的，那么$union.big_(alpha in I) A_(alpha)$也是至多可数的]
#proof[
    当$I = emptyset$时，显然$union.big_(alpha in I)A_alpha$也是至多可数的，接下来讨论$I$非空的情况

    由于$I$是至多可数的，那么有单射$iota:I->NN$，由于任意$alpha in I, A_alpha$也至多可数，那么有单射族$j_alpha:A_alpha -> NN$，定义集合
    $
        S := union.big_(alpha in I) ({alpha} times A_alpha)
    $定义映射$Phi:S->NN times NN, Phi((alpha, x)) = (iota(alpha), j_alpha (x))$，那么$Phi$是单射，由于@coro:NN-times-NN-countable 可知$NN times NN$是可数的，那么$S$是至多可数的

    定义函数$pi:S-> union.big_(alpha in I)A_alpha, pi((alpha, x)) = x$，于是
    $
        pi(S) = {pi(s):s in S} = {x : (alpha, x) in S} = {x : exists alpha in I, x in A_alpha} = union.big_(alpha in I)A_alpha
    $所以$pi$是满射，那么就有
    $
        \#(union.big_(alpha in I)A_alpha) = \#(pi(S)) <= \#(S)
    $由于$\#(S)$是至多可数的，那么$\#(union.big_(alpha in I)A_alpha)$也是至多可数的

]

#problem[找到一个双射$f:NN->QQ$]
#solution[
    由@coro:ZZ-countable 和@coro:countable-cartesian-countable 可知$ZZ times (ZZ without {0})$是可数的，那么存在一个双射$e: NN-> ZZ times ZZ without {0}$，定义一个满射$f:ZZ times (ZZ without {0}) -> QQ, f(a, b) = a/b$，综上就有满射函数
    $
        h = f compose e : NN->QQ
    $
    接下来定义集合
    $
        A_n = {n in NN: h(m) != h(n), forall 0<=m<=n}
    $令$a_n = min(A_n)$，定义函数$h'$是在$A$上的限制，由@proposition:f-NN-countable 的讨论可知$h'$是双射，接着由@proposition:for-X-NN-conuntbale 可知一定存在唯一递增双射$phi:NN->A$，那么$phi compose h': NN->QQ$是双射，即为所求

]

== 无穷集合上的求和

#definition[无穷集合上的级数][
    $X$是一个可数集，$f:X->RR$是一个函数，称级数$sum_(x in X)f(x)$是绝对收敛的，当且仅当存在双射$g:NN->X$，使得级数$sum_(n=0)^oo f(g(n))$是绝对收敛的，并有
    $
        sum_(x in X)f(x) = sum_(n=0)^oo f(g(n))
    $
]<def:infinite-series>

#theorem[无穷级数Fubini定理][
    $f:NN times NN -> RR$是一个函数，且$sum_((n,m) in NN times NN) f(n, m)$绝对收敛，那么就有
    $
        sum_(n=0)^oo (sum_(m=0)^oo f(n,m)) & = sum_((n,m) in NN times NN)f(n,m) \
                                           & = sum_((m,n) in NN times NN) f(n, m) \
                                           & = sum_(m=0)^oo (sum_(n=0)^oo f(n, m))
    $
]
#proof[
    @proposition:absolute-convergent-series-rearrangment 易知$sum_((n,m) in NN times NN)f(n, m) = sum_((m,n) in NN times NN)f(n,m)$成立，因为有双射$g:NN times NN -> NN times NN, g(n,m) = (m,n)$

    对于第一个等式，考虑$f(n, m)$是非负的，由于绝对收敛，令
    $
        L := sum_((n, m) in NN times NN)f(n, m)
    $任取$X subset.eq NN times NN, X "is finite"$，由于@coro:countable-cartesian-countable，可知存在一个双射$g: NN times NN -> NN$，那么$g(X)$是$NN$的有限子集，因此是有界的，所以$sum_((n,m) in X) f(n, m)$有界.

    特别的，任选$n in NN, M in NN$，都有$sum_(m=0)^M f(n, m) <= L$，由于单调有界收敛，可知对任意$n$，$sum_(m=0)^oo f(n, m)$收敛，那么任取$N, M in NN$，根据@coro:fubini-finite-series 就有
    $
        sum_(n=0)^N sum_(m=0)^M f(n, m) = sum_((n, m) in X)f(n, m) <= L
    $其中$X = {(n, m) in NN times NN: n<=N, m<=M}$，由于对任意$M in NN$都成立，且$f(n, m)$是非负的，由单调有界可知
    $
        sum_(n=0)^N sum_(m=0)^oo f(n, m) <= L
    $同样的，对于任意$N$来说也是单调有界的，就有
    $
        sum_(n=0)^oo sum_(m=0)^oo f(n, m) <= L
    $所以确实是收敛的，接下来证明收敛到$L$，由于$sum_((n,m) in NN times NN)f(n,m) = L$那么就有，存在一个有限子集$Y subset.eq NN times NN$满足
    $
        abs(sum_((n, m) in Y) f(n, m) - L) <= epsilon => sum_((n, m) in Y)f(n, m) >= L - epsilon
    $那么取$Y$的有限超集$X:= {(n, m) in NN times NN: n<=N, m<=M}$，就有
    $
        sum_(n=0)^N sum_(m=0)^N f(n, m) = sum_((n,m) in X)f(n, m) >= sum_((n,m) in Y)f(n,m) >= L -epsilon
    $也因此
    $
        sum_(n=0)^oo sum_(m=0)^oo f(n, m) >= sum_(n=0)^N sum_(m=0)^M f(n,m) >= L - epsilon
    $由于$epsilon$是任取的，这说明
    $
        sum_(n=0)^oo sum_(m=0)^oo f(n, m) = L = sum_((n,m) in NN times NN)f(n,m)
    $

    综上考虑了$f(n,m)$非负的情况，对于$f(n,m)$非正的情况，只需要加上负号进行推理即可；对于有正有负的情况，可以将正部、负部分开
    $
        f(n, m) = f_(+)(n, m) + f_(-)(n, m)
    $如果$sum_((n,m) in NN times NN)f(n, m)$绝对收敛，那么每个分部的级数也是绝对收敛的，二者之和也是绝对收敛的
]

#lemma[$X$是一个可数集，$f: X -> RR$是一个函数，那么级数$sum_(x in X)f(x)$绝对收敛，当且仅当
    $
        sup{sum_(x in A) abs(f(x)): A subset.eq X, A "finite"} < oo
    $
]<lemma:countable-series-absolute-convergent>
#proof[
    1. $=>$\
        $sum_(x in X) f(x)$是绝对收敛的，$X$是可数的，那么有双射$g:NN->X$，使得$sum_(n=0)^oo f(g(n))$也绝对收敛，并且有相同的值

        任选$X$的有限子集$A$，其基数为$M$，那么一定有双射$g_A: {i in NN: i<= M-1}->A$，于是
        $
            sum_(x in A) abs(f(x)) = sum_(n=0)^(M-1) abs(f(g_A (n))) <= sum_(n=0)^oo abs(f(g(n))) = sum_(x in X) abs(f(x)) < oo
        $由于$A$是任选的，那么
        $
            sup{sum_(x in A) abs(f(x)) : A subset.eq X, A "finite"} < oo
        $
    2. $arrow.double.l$\
        任取$X$的有限子集$A_N$，基数为$N$，$A_N := {g(i): i in NN, i<=N}$，于是就有
        $
            sum_(x in A_N) abs(f(x)) = sum_(n=0)^N abs(f(g(n)))
        $由于
        $
            sup{sum_(x in A) abs(f(x)): A subset.eq X, A "finite"} < oo
        $那么令$M := sup{sum_(x in A) abs(f(x)): A subset.eq X, A "finite"}, M in RR^+$，就有
        $
            forall N >= 0, sum_(n=0)^N abs(f(g(n))) <= M
        $这说明序列$(sum_(n=0)^N abs(f(g(n))))_(N=0)^oo$单调递增且有上界，那么必然收敛，进而$sum_(x in X)f(x)$绝对收敛
]

#definition[不可数集合上的求和][
    $X$是一个集合（可能是不可数的），$f:X->RR$是函数，称$sum_(x in X)f(x)$是绝对收敛的，当且仅当
    $
        sup{sum_(x in A)abs(f(x)) : A subset.eq X, A "finite"} < oo
    $
]

#lemma[
    $X$是一个集合（可能是不可数的），$f:X->RR$是函数，如果$sum_(x in X) f(x)$绝对收敛，那么集合$Y = {x in X: f(x) != 0}$是至多可数的
]<lemma:non-countable-series-absolute-convergent-non-zero-element-countable>
#proof[
    由于该级数绝对收敛，那么令
    $
        M := sup{sum_(x in A) abs(f(x)): A subset.eq X, A "finite"} in RR^+
    $定义集合
    $
        Z_n := {x in X: abs(f(x)) > 1/n}
    $接下来需要证明，当$n in ZZ^+$时，$Z_n$都是有限的，假设存在一个$Z_n$是无穷的，那么，可以取$Z_n$的、含有$k$个元素的子集$A$，那么就有
    $
        sum_(x in A) abs(f(x)) > k/n
    $于是当$k->+oo$时
    $
        M >= sum_(x in A) abs(f(x)) > k/n > oo
    $矛盾，所以任意$n in ZZ^+$，$Z_n$都是有限的，于是集合
    $
        Z = union.big_(n in ZZ^+)Z_n
    $是至多可数的

    还需要证明$Z = Y$，任取$z in Z$，那么存在$n in ZZ^+$，使得$z in Z_n$，这意味这$abs(f(z)) > 1/n > 0$，于是$z in Y$，所以$Z subset.eq Y$

    任取$y in Y$，那么$f(y) != 0 => abs(f(y)) > 0$，所以存在$n in ZZ^+$，满足$abs(f(y)) > 1/n$，所以$y in Z_n => y in Z$，所以$Y subset.eq Z$，于是$Y = Z$，所以$Y$是至多可数的
]

#proposition[绝对收敛级数定律][
    $X$是一个任意集合，$f:X->RR, g:X->RR$是函数，且$sum_(x in X)f(x), sum_(x in X)g(x)$都绝对收敛，那么有以下成立
    1. $sum_(x in X)(f(x) + g(x))$绝对收敛，且
        $
            sum_(x in X) (f(x) + g(x)) = sum_(x in X)f(x) + sum_(x in X)g(x)
        $
    2. $c in RR$，那么$sum_(x in X)c f(x)$绝对收敛，且
        $
            sum_(x in X)c f(x) = c sum_(x in X)f(x)
        $
    3. 如果$X = X_1 union X_2$且$X_1 inter X_2 = emptyset$，那么
        $
            sum_(x in X_1 union X_2) f(x) = sum_(x in X_1)f(x) + sum_(x in X_2)f(x)
        $同理，如果函数$h:X->RR$满足$sum_(x in X_1)h(x), sum_(x in X_2)h(x)$都是绝对收敛的，那么$sum_(x in X_1 union X_2) h(x)$也是绝对收敛的，且
        $
            sum_(x in X_1 union X_2) h(x) = sum_(x in X_1)h(x) + sum_(x in X_2)h(x)
        $
    4. 如果$Y$是另一个集合，且$phi: Y->X$是双射，那么$sum_(y in Y)f(phi(y))$也是绝对收敛的，且
        $
            sum_(y in Y) f(phi(y)) = sum_(x in X)f(x)
        $
]<proposition:convergent-series-laws>

#lemma[$sum_(n=0)^oo a_n$是一个条件收敛的实数级数，定义集合$A_+ := {n in NN： a_n >= 0}, A_- := {n in NN: a_n < 0}$，那么$A_+ union A_- = NN, A_+ inter A_- = emptyset$，那么$sum_(n in A_+) a_n, sum_(n in A_-) a_n$都不是绝对收敛的]<lemma:conditional-convergent-neg-pos-not-convergent>
#proof[
    由于原级数收敛，那么就有
    $
        sum_(n in NN)a_n = sum_(n in A_+) a_n - sum_(n in A_-)abs(a_n)
    $假设$sum_(n in A_+)a_n$绝对收敛，那么可知$sum_(n in A_-)abs(a_n)$也是收敛的且
    $
        sum_(n in A_-)abs(a_n) = sum_(n in A_+)a_n - sum_(n in NN)a_n
    $也是收敛的，于是
    $
        sum_(n in NN)abs(a_n) = sum_(n in A_+)abs(a_n) + sum_(n in A_-)abs(a_n) < oo
    $这说明$sum_(n in NN)a_n$是绝对收敛的，与条件矛盾

    同上假设$sum_(n in A_+)a_n$绝对收敛，也会得到矛盾.
    综上，条件收敛的级数，其正/负部的子级数都不会是绝对收敛的

]


// #theorem[$sum_(n=0)^oo a_n$是一个条件收敛的序列，$L in RR$，那么存在双射$f: NN->NN$使得$sum_(m=0)^oo a_(f(m))$条件收敛到$L$]
// #proof[
//     定义集合
//     $
//         A_+ := {n in NN: a_n >= 0}\
//         A_- := {n in NN: a_n < 0}\
//     $由@lemma:conditional-convergent-neg-pos-not-convergent 可知$sum_(n in A_+)a_n$和$sum_(n in A_-)a_n$都不是绝对收敛的
//
//     此外，由于$A_+, A_-$都是$NN$的无穷子集，那么由@proposition:for-X-NN-conuntbale 可知有单调递增的双射函数$f_+:NN->A_+$和$f_-:NN->A_-$，于是
//     $
//         sum_(m=0)^oo a_(f_+(m)) = sum_(n in A_+)a_n\
//         sum_(m=0)^oo a_(f_-(m)) = sum_(n in A_-)a_n\
//     $都不是绝对收敛的
//
//     接下来按照如下规则，递归的定义序列$n_0, n_1,...$
//     - 如果$sum_(i=0)^(j-1) a_(n_i) < L$，则定义
//         $
//             n_j := min{n in A_+: n!=n_i, forall i < j}
//         $
//     - 如果$sum_(i=0)^(j-1) a_(n_i) >=L$，则定义
//         $
//             n_j := min{n in A_-: n!=n_i, forall i <= j}
//         $
//     直觉上，如果级数比$L$小，就加进去一个正数放大，如果大于$L$，就加进去一个负数拉低
//
//     首先证明$g:NN->NN, j|->n_j$是一个单射，任取$n_k = n_m$，如果$n_k, n_m in A_-$，那么
//     $
//         n_k = min{n in A_-: n!=n_i, forall i < k}\
//         n_m = min{n in A_-: n!=n_i, forall i < m}\
//     $由@proposition:well-ordering-principle 可知只能是$k=m$，如果$n_k,n_m in A_+$同理也有$k = m$，如果$n_k in A_+, n_m in A_-$，那么就有
//     $
//         n_k = min{n in A_+: n!=n_i, forall i < k}\
//         n_m = min{n in A_-: n!=n_i, forall i < m}\
//     $由于$A_+ inter A_- = emptyset$，所以$n_k != n_m$，与条件矛盾，综上$g$是单射
// ]

#problem[证明@lemma:countable-series-absolute-convergent][见前]
#problem[证明@lemma:non-countable-series-absolute-convergent-non-zero-element-countable][见前]
#problem[证明@proposition:convergent-series-laws]
#proof[
    由于$sum_(x in X)f(x), sum_(x in X)g(x)$都绝对收敛，所以定义
    $
        F := sup{sum_(x in A)abs(f(x)) : A subset.eq X, A "finite"} in RR^+\
        G := sup{sum_(x in A)abs(g(x)) : A subset.eq X, A "finite"} in RR^+\
    $同时易知以下两个集合都是可数的
    $
        X_f := {x in X: f(x) != 0}\
        X_g := {x in X: g(x) != 0}
    $

    1. 对于级数$sum_(x in X)(f(x) + g(x))$，定义集合
        $
            T := {sum_(x in A) abs(f(x) + g(x)): A subset.eq X, A "finite"}
        $对任意的有限子集$A$都有
        $
            sum_(x in A) abs(f(x) + g(x)) <= sum_(x in A)abs(f(x)) + sum_(x in A)abs(g(x))
        $于是
        $
            sup(T) <= F + G < oo
        $于是$sum_(x in X)(f(x) + g(x))$是绝对收敛的，级数和可以看作只由非零项贡献，于是定义集合
        $
            X_(f+g) := {x in X: f(x) + g(x) != 0} subset.eq X_f union X_g
        $易知$X_(f+g)$是至多可数的，令$S:= X_f union X_g$所以
        $
            sum_(x in X)(f(x) + g(x)) & = sum_(x in X_(f+g))(f(x) + g(x)) = sum_(x in S)(f(x) + g(x)) \
            sum_(x in X)f(x) & = sum_(x in X_f)f(x) = sum_(x in S)(f(x))\
            sum_(x in X)g(x) & = sum_(x in X_g)g(x) = sum_(x in S)(g(x))\
        $由可数无穷级数定律易有
        $
            sum_(x in S)(f(x) + g(x)) = sum_(x in S) f(x) + sum_(x in S)g(x)
        $于是
        $
            sum_(x in X)(f(x) + g(x)) = sum_(x in X) f(x) + sum_(x in X)g(x)
        $

    2. 定义集合
        $
            T := {sum_(x in A) abs(c f(x)): A subset.eq X, A "finite"}
        $于是对$X$的任意有限子集都有
        $
            sum_(x in A)abs(c f(x)) = abs(c) sum_(x in A)abs(f(x))
        $于是
        $
            sup(T) = abs(c)F < +oo
        $于是$sum_(x in X)c f(x)$是绝对收敛的，由于集合$X_f$是至多可数的，那么
        $
            sum_(x in X)c f(x) = sum_(x in X_f)c f(x) = c sum_(x in X_f)f(x) = c sum_(x in X)f(x)
        $
    3. (整体到部分和)由于$sum_(x in X)f(x)$绝对收敛，由于$X = X_1 union X_2$，那么
        $
            sum_(x in X_1)abs(f(x)) <= sum_(x in X)abs(f(x))
        $同理$X_2$，所以$sum_(x in X_1)f(x)$和$sum_(x in X_2)f(x)$都是绝对收敛的，取$S_1 = X_f inter X_1, S_2 = X_f inter X_2$，易知$S_1,S_2$都是至多可数的，且$S_1 inter S_2 = emptyset, S_1 union S_2 = X_f$，于是就有
        $
            sum_(x in X)f(x) = sum_(x in X_f)f(x) = sum_(x in S_1)f(x) + sum_(x in S_2)f(x) = sum_(x in X_1)f(x) + sum_(x in X_2)f(x)
        $
    3. (部分和到整体)由于$sum_(x in X_1)h(x)$和$sum_(x in X_2)h(x)$都是绝对收敛的，那么下列两个集合都是至多可数的
        $
            X_h^1 := {x in X_1: h(x) != 0}\
            X_h^2 := {x in X_2: h(x) != 0}\
        $并且易知${x in X_1 union X_2: h(x) != 0 } = X_h^1 union X_h^2$，这也是至多可数的，并且$X_h^1 inter X_h^2 = emptyset$，所以根据可数无穷级数定律就有
        $
            sum_(x in X_1 union X_2)h(x) = sum_(x in X_h^1 union X_h^2)h(x) = sum_(x in X_h^1)h(x) + sum_(x in X_h^2)h(x) = sum_(x in X_1)h(x) + sum_(x in X_2)h(x)
        $
    4. 由于$phi:Y->X$是一个双射，那么$phi^(-1)$存在，且$Y_f = phi^(-1)(X_f) subset.eq Y$也是一个至多可数集合，此外有$X_f = phi(Y_f)$，那么就有
    $
        sum_(y in Y)f(phi(y)) =sum_(y in Y_f)f(phi(y)) = sum_(x in X_f)f(x) = sum_(x in X)f(x)
    $

]

#problem[证明@lemma:conditional-convergent-neg-pos-not-convergent][见前]

#note-block[原书习题8.2.5/8.2.6跳过]

== 不可数集合

#theorem[Cantor 定理][
    $X$是一个任意集合，那么$X$和$2^X$不会有相同的基数
]<theorem:cantor-powerset-set-not-eq>
#proof[
    假设$X$与$2^X$有相同的基数，那么有一个双射$f: X->2^X$，定义一个集合
    $
        A := {x in X: x in.not f(x)}
    $$f(x) in 2^X$，因此$f(x)$是一个$X$的子集，同时显然$A$也是$X$的一个子集，那么$A in 2^X$

    由于$f$是双射，那么存在$x in X$使得$f(x) = A$，对于$x$和$A$来说有两种可能
    - $x in A$，那么由$A$的定义，$x in.not f(x) = A$，矛盾
    - $x in.not A$，那么由$A$的定义，$x in.not f(x)$，那么$x in A$，矛盾

    所有情况都是矛盾的，所以$X$和$2^X$不会有相同的基数
]

#corollary[$2^NN$是不可数的]
#proof[
    由@theorem:cantor-powerset-set-not-eq 可知$NN$和$2^NN$没有相同的基数，所以$2^NN$不是可数的，所以是不可数或有限的

    同时定义一个集合
    $
        S := {{i} : i in NN}
    $易知$S subset.eq 2^NN$，并且有双射$g: NN -> S, g(n) = {n}$，所以$S$是可数的，那么$2^NN$就不可能是有限的，综上$2^NN$是不可数的
]

#corollary[$RR$是不可数的]
#proof[
    定义函数$f: 2^NN ->RR$为
    $
        f(A) := sum_(n in A)10^(-n)
    $由@lem:geometry-series 可知$sum_(n=0)^oo 10^(-n)$是绝对收敛的，那么函数$f$也是良定义的，现在假设$f$不是一个单射，来寻找矛盾，比如有两个集合$A != B$，但是$f(A) = f(B)$.

    令$S := (A without B) union (B without A)$，由于$A != B$，那么$S subset.eq 2^NN$并且是非空的，那么由@proposition:well-ordering-principle 可知有$n_0 := min(S)$，所以$n_0 in A without B or n_0 in B without A$

    不妨设$n_0 in A without B$，那么$n_0 in A and n_0 in.not B$，那么对于任意$n < n_0$就有$n in A, B or n in.not A, B$，因此就有
    $
        0 & = f(A) - f(B) \
          & = sum_(n in A)10^(-n) + sum_(n in B)10^(-n) \
          & = (sum_(n<n_0 : n in A)10^(-n) + 10^(-n_0) + sum_(n>n_0:n in A)10^(-n))
            - (sum_(n<n_0:n in B)10^(-n) + sum_(n>n_0:n in B)10^(-n))
    $由于$n < n_0$，那么$n$只能同时在$A,B$中，或同时不在$A,B$中，所以总有
    $
        sum_(n < n_0: n in A)10^(-n) = sum_(n < n_0: n in B)10^(-n)
    $于是就有
    $
        0 & = f(A) - f(B) \
          & = 10^(-n_0) + sum_(n > n_0: n in A)10^(-n) - sum_(n > n_0: n in B)10^(-n) \
          & >= 10^(-n_0) + 0 - sum_(n > n_0)10^(-n)
    $这里是两次放缩，$sum_(n>n_0:n in A)10^(-n) > 0$，然后是$-sum_(n > n_0 : n in B) 10^(-n) > -sum_(n > n_0)10^(-n)$，这是因为${n > n_0: n in B} subset.eq {n > n_0: n in NN}$

    根据几何级数的计算就有
    $
        sum_(n > n_0) 10^(-n) = sum_(m=0)^oo 10^(-(n_0 + 1 + m)) = 10^(-(n_0 + 1))sum_(m=0)^oo 10^(-m) =10^(-(n_0 + 1)) * 10/9 = 10^(-n_0)/9
    $代入到原式就有
    $
        0 = f(A) - f(B) >= 10^(-n_0) - 10^(-n_0)/9 > 0
    $矛盾，所以$f$一定是单射，这说明$f(2^NN)$和$2^NN$有相同的基数，都是不可数的，而$f(2^NN) subset.eq RR$，那么$RR$也一定是不可数的
]

#problem[$X$是一个有限集合，基数为$n$，证明$2^X$也是一个有限集合，且基数为$2^n$]
#proof[
    对$n$进行归纳，当$n=0$时，$X = emptyset, 2^X = {emptyset}$，有$\#({emptyset}) =1 = 2^0$

    归纳性的假设$n$时成立，$\#(X) = n, \#(2^X) = 2^n$，现在证明$n+1$的情况，令$X' = X union {x_0}, x_0 in.not X, \#(X') = n+1$

    定义一个函数$g:2^X times {{x_0}, emptyset} -> 2^(X'), g(T, W) = T union W$，令$g$的像为$G$，于是就有
    $
        G &:= g(2^X times {{x_0}, emptyset})\ &= {T union {x_0}: forall T in 2^X} union {T union emptyset: forall T in 2^X}\ &= {T union {x_0}: forall T in 2^X} union 2^X
    $任选$S in 2^(X')$，如果$x_0 in S$，那么$S without {x_0} in 2^X$，于是有$S in {T union {x_0}: forall T in 2^X}$；如果$x_0 in.not S$，那么$S in 2^X$，所以$S in G$

    任选$P in G$，如果$P in 2^X$，那么$P in 2^X'$，如果$P in {T union {x_0}: forall T in 2^X}$，那么$P in 2^X'$，所以$P in 2^X'$，综上就有$G = 2^X'$，所以$\#(2^X') = \#(G)$

    又因为$x_0 in.not X$，那么${T union {x_0}: forall T in 2^X} inter 2^X = emptyset$，所以$\#(G) = \#(2^X) + \#({T union {x_0}: forall T in 2^X})$

    易有双射函数$h: {T union {x_0}: forall T in 2^X} -> 2^X, h(t) = t without {x_0}$，所以$\#(2^X times {x_0}) = \#(2^X)$，代入归纳假设就有
    $
        \#(2^X') & = \#({T union {x_0}: forall T in 2^X}) + \#(2^X) \
                 & = 2^n + 2^n \
                 & = 2^(n+1)
    $
    归纳结束
]

#problem[$A,B,C$是集合且$A subset.eq B subset.eq C$，有单射$f:C->A$，递归的定义集合
    $
        D_0 := B without A, D_(n+1) := f(D_n), n in NN
    $证明$forall n,m in NN, n!=m, D_n inter D_m = emptyset$

    进一步的，定义函数
    $
        g(x) = cases(f^(-1)(x) &\, x in union.big_(n=1)^oo D_n, x &\, x in.not union.big_(n=1)^oo D_n)
    $证明$g$将$A$中元素都映射到了$B$中，且$g:A->B$是双射
]
#proof[
    假设$exists k, j in NN, 1<= j < k, D_j inter D_k != emptyset$，那么任取$d in D_j inter D_k$，由于$f$是单射，那么存在
    $
        m_(k-1) in D_(k-1), f(m_(k-1)) = d
    $同理也存在
    $
        n_(j-1) in D_(j-1), f(n_(j-1)) = d
    $由于$f$是单射，那么$m_(k-1) = n_(j-1)$，这说明$D_(k-1) inter D_(j-1) != emptyset$，于是重复这个过程，就有$D_(k-j) inter D_0 != emptyset$

    由于$f:C->A$，那么$f(C) subset.eq A$，由于$A subset.eq B$，那么$B without A inter A = emptyset$，但是由于$D_(n+1) = f(D_n) subset.eq A$，那么$D_0 inter D_(n) = emptyset, n>=1$，与$D_(k-j) inter D_0 != emptyset$矛盾，所以假设不成立，所以$D_n, n in NN$两两不相交.

    接下来证明$g$将所有$A$映射到$B$中
    - $x in union.big_(n=1)^oo D_n$时，由于$D_n$两两不相交，那么唯一有一个$D_k$使得$x in D_k$，那么$g(x) = f^(-1)(x) in D_(k-1) = f(D_k) subset.eq A subset.eq B$
    - $x in.not union.big_(n=1)^oo D_n$时，$g(x) = x subset.eq A subset.eq B$
    于是$g$确实将$A$映射到$B$中，接下来证明是双射

    - 首先证明是单射，取$x, y in A$，令$g(x) = g(y)$
        - $x, y in union.big_(n=1)^oo D_n$时,由于$D_n$两两不相交，那么存在唯一的$k, j$使得
            $
                g(x) = f^(-1)(x) in D_(k-1)\
                g(y) = f^(-1)(y) in D_(j-1)\
            $如果$g(x) = g(y)$，那么只能是$k - 1 = j - 1 => k = j$，于是$x, y in D_k$，那么
            $
                f(f^(-1)(x)) = f(f^(-1)(y)) => x = y
            $
        - $x, y in.not union.big_(n=1)^oo D_n$，此时
            $
                g(x) = x , g(y) = y
            $自然有$x = y$
        - $x in union.big_(n=1)^oo D_n, y in.not union.big_(n=1)^oo D_n$时，不妨令$x in D_k$，那么$g(x) = f^(-1)(x) in D_(k-1), g(y) = y$，如果$g(x) = g(y)$，那么说明$y in D_(k-1)$，如果$k-1>0$，这和假设的$y in.not union.big_(n=1)^oo D_n$，矛盾；如果$k-1=0=>k=1$，那么$y in D_0 = B without A$，矛盾，所以这种情况不可能发生
        - 综上，所有情况下都有$g(x) = g(y) => x = y$，所以$g$是单射
    - 接下来证明$g$是满射，任取$y in B$，由于$B = A union D_0, A inter D_0 = emptyset$，所以分开讨论
        - $y in A$时
            - $y in union.big_(n=1)^oo D_n$时，由于$D_n$两两不相交，不妨令$y in D_k$，由于$D_k = f(D_(k-1))$，那么存在$x in D_(k-1)$使得$f(x) = y$，那么$g(y) = f^(-1)(f(x)) = x in union.big_(n=1)^oo D_n$，成立
            - $y in.not union.big_(n=1)^oo D_n$，那么取$x = y$，就有$g(y) = g(x) = x$，成立
        - $y in D_0$时，就有$y in D_0 subset.eq B subset.eq C$，那么$x = f(y) in f(D_0) = D_1 subset.eq union.big_(n=1)^oo D_n$，于是$g(x) = f^(-1)(f(y)) = y$，于是确实有$x = f(y) in A$使得$g(x) = y$
        - 综上，各种情况下都有$x$使得$y = g(x)$

    所以$g$是双射，进而$A$和$B$有相同的基数
]

#problem[
    称$A$的基数小于等于$B$，当且仅当有$A$到$B$的单射

    如果$A$的基数小于等于$B$且$B$的基数小于等于$A$，那么$A$和$B$有相同的基数
]
#proof[
    由上一个问题，若$A subset.eq B subset.eq C$且有$C->A$的单射，那么$A,B$间存在双射.

    由于$\#(A) <= \#(B) and \#(B) <= \#(A)$，那么存在两个单射$i:A->B, j:B->A$，接着令$B' := (B without i(A) ) union A$，定义函数$h:B' -> B$为
    $
        h(x) = cases(x &\, x in B without i(A), i(x) &\, x in A)
    $由于$i$是单射，易知$h:B'->B$是双射，那么$\#(B) = \#(B')$，同时显然有$A subset.eq B'$

    接下来构造$B'->A$的单射，易知$f:j compose h$是一个单射，接下来令$C = B'$，那么就有
    $
        A subset.eq B = B' and f "单射"
    $于是一定有$A,B$之间的双射，进一步的$A$和$B$有相同的基数
]

#problem[
    称集合$A$的基数严格小于$B$，当且仅当$A$的基数小于等于$B$的级数并且$A$的基数不等于$B$的基数.

    证明：$X$是一个集合，那么$X$的基数严格小于等于$2^X$的基数

    证明：$A$的基数严格小于等于$B$的基数，$B$的基数严格小于等于$C$的基数，那么$A$的基数严格小于等于$C$的基数
]
#proof[
    1. 定义函数$g: X -> 2^X, g(x) = {x}$，易知$g$是单射，那么$X$的基数小于等于$2^X$，由@theorem:cantor-powerset-set-not-eq 可知，$X$不可能与$2^X$有相同的基数，所以$X$的基数严格小于$2^X$的基数
    2. $A$的基数严格小于等于$B$的基数，$B$的基数严格小于等于$C$的基数，那么存在两个单射$i: A->B, j:B->C$，于是也有单射$k:A->C, k = j compose i$，所以$\#(A) <= \#(C)$，假设存在双射$t:A->C$，那么$t^(-1) compose j: B->A$是单射，又因为$i:A->B$是单射，这说明$A,B$之间存在双射，所以$A$和$B$有相同基数，与条件矛盾，所以$\#(A) < \#(C)$
]

#problem[证明没有一个集合的幂集是可数无穷的][
    - 如果$X$是有限的，那么$2^X$也是有限的，不是可数无穷
    - 如果$X$是可数无穷的，假设$2^X$是可数无穷的，那么有两个双射$g: NN -> X, f: NN -> 2^X$，于是有双射$f compose g^(-1): X -> 2^X$是双射，这说明$X$和$2^X$有相同的基数，这和@theorem:cantor-powerset-set-not-eq 矛盾
    - 如果$X$是不可数的，有单射$g: X -> 2^X, g(x) = {x}$，所以$\#(X) <= \#(2^X)$，那么$2^X$也是不可数的

    综上没有一个集合的幂集是可数无穷的
]

== 选择公理

#definition[无穷笛卡尔积][
    $I$是一个集合，任意$alpha in I, X_alpha$也是一个集合，定义无穷笛卡尔积为
    $
        product_(alpha in I) X_alpha = {(x_alpha)_(alpha in I) in (union.big_(beta in I)X_beta)^I: x_alpha in X_alpha, forall alpha in I}
    $
]

无穷笛卡尔积实际上是下面这个集合的子集
$
    (union.big_(beta in I)X_beta)^I = {f: I->union.big_(beta in I)X_beta}
$
但是这个集合太大了，所以加了一个限制，对于指标集中的一个元素$alpha$，希望函数$f(alpha) in X_alpha$

接下来将这些函数写成紧凑的函数族形式，也即
$
    (x_alpha)_(alpha in I) : I -> union.big_(beta in I)X_beta
$$(x_alpha)_(alpha in I)$是函数，$x_alpha$是该函数在$alpha$处的求值

之所以要用这样繁琐的形式是为了处理不可数无穷个集合，对于有限个集合，我可以显式的枚举每一个集合，并从中取一个元素；对于可数无穷个集合，可以使用自然数为索引在每个集合中选一个，但是不可数无穷的集合，枚举和自然数索引都失效了，只能以函数的形式呈现.

#axiom[选择公理][
    $I$是集合，$forall alpha in I, X_alpha != emptyset => product_(alpha in I)X_alpha != emptyset$，也即存在函数$(x_alpha)_(alpha in I)$为每一个$alpha in I$分配一个元素$x_alpha in X_alpha$
]
这个公理意味这，对于（不）可数无穷多的非空集合，可以在每个集合中取一个元素，然后将取出元素拼接为一个（不）可数无穷长的元组.


#lemma[选择公理应用1][$E$是实数的非空子集，并且$sup(E) < +oo$，那么存在一个序列$(a_n)_(n=1)^oo$，满足$forall a_n in E$且$lim_(n->oo)a_n = sup(E)$]
#proof[
    定义集合
    $
        forall n in ZZ^+, X_n := {x in E: sup(E) - 1/n <= x <= sup(E)}
    $易知任意正整数，$X_n$都是非空的，那么利用选择公理就可以得到序列$(a_n)_(n=1)^oo$满足，这里$ZZ^+$扮演了指标集的角色，$X_n$则是待选择的可数无穷多的集合
    $
        forall n in ZZ^+, a_n in X_n
    $于是就有
    $
        forall n in ZZ^+, sup(E) -1/n <= a_n <= sup(E)
    $由夹逼定理易有
    $
        lim_(n->oo) a_n = sup(E)
    $
]
选择公理爆率真的很高！

#problem[$X, Y$是集合，$P(x, y)$是一个有关$x in X, y in Y$的性质，对于任意$x in X$，存在$y in Y$，使得$P(x, y)$成立，那么存在一个函数$f:X -> Y$，使得对于任意$x in X$，都有$P(x, f(x))$成立]
#proof[
    以$X$为指标集，定义如下集合
    $
        Y_x = {y in Y: P(x, y)}
    $由于任意$x in X$，都存在$y in Y$使得$P(x, y)$成立，那么$forall x in X, Y_x != emptyset$，于是使用选择公理，可以得到函数
    $
        f: X -> union.big_(x in X)Y_x subset.eq Y
    $该函数满足$f(x) in Y_x$，所以确实存在这样的函数$f$满足条件
]

#problem[$I$是一个集合，$forall alpha in I, X_alpha != emptyset$，并且任意$X_alpha$两两不相交
    + 使用选择公理证明存在集合$Y$满足$\#(Y inter X_alpha) = 1, forall alpha in I$
    + 对任意一族非空集合(可能相交)，如果存在上述的$Y$，那么选择公理是正确的
]
#proof[
    + 由于任意$X_alpha$非空，由选择公理可以定义函数
        $
            f:I->union.big_(alpha in I)X_alpha, f(alpha) = x_alpha in X_alpha
        $定义集合$Y := {f(alpha) : forall alpha in I}$，由于$X_alpha$两两不相交，那么$Y inter X_alpha = {x_alpha} => \#(Y inter X_alpha) = 1$，所以确实存在这样的集合

    + 定义新的集合
        $
            X'_alpha = {alpha} times X = {(alpha, x): x in X_alpha}
        $这样任意$X'_alpha$两两不相交，由条件存在$Y$使得$\#(Y inter X'_alpha) = 1$，那么令
        $
            (alpha, x_alpha) := Y inter X'_alpha
        $接下来定义函数
        $
            f: I-> union.big_(alpha in I)X_alpha, f(alpha) = x_alpha
        $其中$x_alpha$由$alpha$唯一确定，所以确实存在这样的函数，于是选择公理是正确的
]

#problem[集合$A, B$之间存在满射$g:B->A$，使用选择公理证明存在单射$f:A->B$，使得$g compose f = id_A$]
#proof[
    由于$g:B->A$是满射，那么对于任意$a in A$，集合
    $
        B_a = {b in B: g(b) = a}
    $非空，根据选择公理，有函数
    $
        f: A-> union.big_(a in A)B_a, f(a) in B_a
    $接下来验证$g compose f = id_A$，任意$a in A$，$f(a) in B_a = g^(-1)({a})$，于是
    $
        g(f(a)) = a
    $接下来验证$f$是单射，取$a, a' in A$，令$f(a) = f(a')$，两边同时作用$g$就有
    $
        g(f(a)) = g(f((a')) => a = a'
    $所以$f$是单射
]

== 有序集

#definition[偏序集(Partially ordered subset/poset)][
    偏序集是一个配备了$scripts(<=)_X$关系的集合$X$，这个关系满足如下三条性质
    + (自反性) $forall x in X, x scripts(<=)_X x$
    + (反对称性) $x, y in X, x scripts(<=)_X y and y scripts(<=)_X x => x = y$
    + (传递性) $x, y, z in X, x scripts(<=)_X y and y scripts(<=)_X z => x scripts(<=)_X z$

    我们将这样的关系$scripts(<=)_X$称作是$X$上的序关系
]
#tip-block[
    + 在$NN, ZZ, QQ, RR, RR^*$上使用的$<=$关系都是序关系
    + $subset.eq$是集合上的序关系
]

#definition[全序集(Totally ordered set/chain)][
    $X$是一个有偏序关系$scripts(<=)_X$的集合，其子集$Y$被称作是全序的，当且仅当
    $
        forall y, y' in Y => y scripts(<=)_X y' or y' scripts(<=)_X y
    $如果$X$本身就是全序的，则称$X$是配备了序关系$scripts(<=)_X$的全序集
]
#tip-block[
    + 同样的，在$NN, ZZ, QQ, RR, RR^*$上的$<=$也是全序的
    + 在集合上的$subset.eq$就不一定是全序的了，比如$X = {{5}, {1,2}, {2,3}, {2}, {2,3,4}$中，${2, 3}, {1, 2}$之间无法用$subset.eq$进行比较，因为${2, 3} subset.eq.not {1, 2}$
    + 偏序集比较宽松，允许有无法比较的元素对；全序集很严格，任意的两个元素之间都要可以进行比较
]

#definition[极大元/极小元(Maximal/Minimal elements)][
    $X$是一个偏序集，$Y subset.eq X$，称$y in Y$是$Y$的极小元，当且仅当不存在$y' in Y$，使得$y' < y$；称$y in Y$是$Y$的极大元，当且仅当不存在$y' in Y$，使得$y < y'$
]
#tip-block[
    对于集合$X = {{5}, {1,2}, {2,3}, {2}, {2,3,4}$，和$X$上的关系$subset.eq$来说，${2}$是极小元，因为没有任何一个其他元素满足$y subset.eq {2}$；极大元是${1, 2}$和${2, 3, 4}$，因为没有其他元素可以包含这两个集合了；${5}$即是极大元也是极小元，因为${5}$即不被任何其他元素包含，也不包含其他任何元素
]

#definition[良序集][
    $X$是一个偏序集，$Y subset.eq X$是一个全序集，称$Y$是良序集，当且仅当$Y$的任意非空子集$Z$都有极小元$min(Z)$
]
#tip-block[
    + $NN$是良序集，但是$ZZ,QQ,RR$都不是
    + 每个有限的全序集都是良序集
    + 良序集的任意子集都是良序的
]

#proposition[强归纳法原理][
    $X$是配备了关系$scripts(<=)_X$的良序集，令$P(n)$是一个有关$n in X$的性质，如果任意$n in X$，都有如下蕴含
    $
        (forall m scripts(<)_X n, P(m)) => P(n)
    $那么$P(n)$对任意$n in X$均为真
]

















#pagebreak()
