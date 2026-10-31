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
    定义一个自然数序列$(a_n)_(n=0)^infinity$，每一项如下
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

    接下来证明序列$(a_n)_(n=0)^infinity$是单调递增的，也即$a_n < a_(n+1), forall n in NN$成立，对$n$归纳，当$n = 0$时
    $
        a_0 = min(X), a_1 = min(X without {a_0})
    $假设$a_0 >= a_1$，由$a_n$的定义，总有$a_m != a_n, forall m!=n$，此外可以得到$a_1 = min(X)$，这说明存在两个不同的自然数都是该子集的最小值，与@proposition:well-ordering-principle 矛盾，所以$a_0 < a_1$

    归纳性的假设$n$时成立，现在证明$n+1$的情况
    $
        a_(n+2) = min{x in X: x != a_m, forall m < n+2} = min(X without {a_m: forall m < n+2})
    $类似与$n=0$时的讨论，就有$a_(n+1) < a_(n+2)$，归纳结束

    定义函数$f: NN -> X, f(n) = a_n$，由上可知，$f$单调递增，因为$a_m!=a_n, forall m !=n$，所以$f$是单射.

    接下来证明$f$是满射，任取$x in X$，假设任意$n in NN$，都有$x != a_n$，这意味这$forall n in NN, x in {x in X: x!= a_m, forall m < n}$，由$a_n$定义，就有$forall n in NN, x > a_n$.

    接下来需要证明一个额外的引理：$(a_n)_(n=0)^infinity$是严格单调递增自然数序列，那么总有$a_n >= n$成立，对$n$进行归纳，$n=0$时，$a_0 >= 0$总成立，因为任意自然数都大于等于$0$，归纳性的假设$n$时成立，那么就有$a_n >= n$，现在证明$n+1$的情况，由于$(a_n)_(n=0)^infinity$单调递增，所以就有
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
#proof[这个证明需要选择公理，暂时搁置.]

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
#proof[这个证明需要选择公理，暂时搁置.]

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






#pagebreak()
