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
]<lemma:closure-basic-property>
#proof[
    + 任选$x in X$，存在元素$x in X$，使得$abs(x - x) = 0$，小于任意正实数，所以$x in overline(X)$，于是$X subset.eq overline(X)$
    + 任选$x in overline(X union Y)$，就有
        $
            forall epsilon in RR^+, exists y in X union Y, abs(x - y) <= epsilon
        $如果$y in Y$，那么就有
        $
            abs(x - y) <= epsilon
        $这说明$x in overline(Y)$，同理如果$y in X$就有$x in overline(X)$，所以$x in overline(X) union overline(Y)$，所以$overline(X union Y) subset.eq overline(X) union overline(Y)$

        任选$x in overline(X) union overline(Y)$，如果$x in overline(X)$，那么
        $
            forall epsilon in RR^+, exists y in X, abs(x - y) <= epsilon
        $由于$y in X => y in X union Y$，这说明$x in overline(X union Y)$，同理如果$x in overline(Y)$也有$x in overline(X union Y)$，所以$overline(X) union overline(Y) subset.eq overline(X union Y)$.
        综上就有$overline(X union Y) = overline(X) union overline(Y)$
    + 任选$x in overline(X inter Y)$，就有
        $
            forall epsilon in RR^+, exists y in X inter Y, abs(x - y) <= epsilon
        $由于$y in X and y in Y$，那么就有
        $
            forall epsilon in RR^+, exists y in X, abs(x - y) <= epsilon=> x in overline(X) \
            forall epsilon in RR^+, exists y in Y, abs(x - y) <= epsilon=> x in overline(Y)
        $所以$x in overline(X) inter overline(Y)$，所以$overline(X inter Y)subset.eq overline(X) inter overline(Y)$

    + 任取$x in overline(X)$，就有
        $
            forall epsilon in RR^+, exists y in X, abs(x - y) <= epsilon
        $由于$X subset.eq Y$，那么$forall x in X, x in Y$，所以就有
        $
            forall epsilon in RR^+, exists y in Y, abs(x - y) <= epsilon
        $所以$x in overline(Y)$，综上就有$overline(X) subset.eq overline(Y)$
]

#lemma[区间的闭包][
    + $a, b in RR, a < b$，$I$是区间$(a,b),[a,b],(a,b],[a,b)$之一，那么$I$的闭包是$[a,b]$
    + $(a, oo), [a, oo)$的闭包是$[a, oo)$
    + $(-oo, a), (-oo, a]$的闭包是$(-oo, a]$
    + $(-oo, oo)$的闭包是$(-oo, oo)$
]
#proof[
    只证明$overline((a, b)) = [a, b]$

    任选$x in [a, b]$，如果$x in (a, b)$，那么显然$x in overline((a, b))$；如果$x = a$，对于任意的$epsilon in RR^+$，取$y = min(a + epsilon/2, (b+a)/2) in (a, b)$，如果$y = a + epsilon/2$，那么就有
    $
        abs(a - y) = abs(epsilon/2) <= epsilon
    $如果$(a+b)/2 < a + epsilon/2 => 0 <b -a < epsilon$就有
    $
        abs(a - y) = abs((a-b)/2) < epsilon/2 <= epsilon
    $所以${a} in overline((a, b))$，同理${b} in overline((a, b))$，所以$[a, b] subset.eq overline((a, b))$

    假设存在$overline((a, b))$的元素不在$[a, b]$中.
    $x > b$时，$forall y in (a, b), x > b > y$，那么$abs(x - y) > 0 => exists epsilon in RR^+, abs(x - y) >= epsilon > 0$，所以这种情况下$x in.not overline((a, b))$，矛盾.
    $x < a$时同理得到矛盾，所以任意$overline((a, b))$中元素一定在$[a,b]$中

    综上$overline((a, b)) = [a, b]$
]


#lemma[常用集合的闭包][
    + $overline(NN) = NN$
    + $overline(ZZ) = ZZ$
    + $overline(QQ) = RR$
    + $overline(RR) = RR$
    + $overline(emptyset) = emptyset$
]<lemma:common-set-closure>
#proof[
    + 由@lemma:closure-basic-property 可知，$NN subset.eq overline(NN)$.
        任取$x in overline(NN)$，如果$x< 0$，那么$forall y in NN, y > x => abs(y - x) > 0 => exists epsilon in RR^+, abs(y - x) >= epsilon > 0$，所以这样的$x$不在$overline(NN)$中.
        如果$x > 0 and x in.not NN$，那么$exists n in NN$使得
        $
            n < x < n+ 1
        $取$y in NN$，如果$y <= n$，那么
        $
            abs(x - y) > 0 => exists epsilon in RR^+, abs(x - y) >= epsilon > 0
        $如果$y > n => y >= n+1$，那么
        $
            abs(y - x) > 0 => exists epsilon in RR^+, abs(y - x) >= epsilon > 0
        $所以这种情况下$x$都不是$NN$的闭包中的元素，综上$overline(NN)$的元素都在自然数中，所以$overline(NN) = NN$

    + 定义集合$-NN := {-i: i in NN}$，易知$overline(-NN) = -NN$，由于$ZZ = -NN union NN$，那么
        $
            overline(ZZ) = overline(-NN union NN) = overline(-NN) union overline(NN) = -NN union NN = ZZ
        $
    + $forall x in RR, forall epsilon in RR^+$，由有理数的稠密性，就存在$q in QQ$，满足
        $
            abs(x - q) <= epsilon
        $这说明$x in overline(QQ)$，于是$RR subset.eq overline(QQ)$，由$overline(QQ)$的定义，自然有$overline(QQ) subset.eq RR$，综上说明$overline(QQ) = RR$

    + 易有$RR subset.eq overline(RR)$，结合$overline(RR)$的定义，就有$overline(RR) subset.eq RR$，于是$overline(RR) = RR$

    + 根据定义
        $
            overline(emptyset) = {x in RR: forall epsilon in RR^+, exists y in emptyset, abs(x - y) <= epsilon}
        $由于$exists y in emptyset$总为假，所以对于任意$x$，上述条件恒为假，于是
        $
            overline(emptyset) = emptyset
        $
]

#lemma[$X subset.eq RR, x in RR, x in overline(X) <=> exists (a_n)_(n=1)^oo subset.eq X , lim_(n->oo)a_n = x$]<lemma:lim-lang-for-closure>
#proof[
    1. $=>$\
        如果$x in overline(X)$，那么
        $
            forall epsilon in RR^+, exists y in X, abs(x - y) <= epsilon
        $对任意$n in NN^+$，定义集合
        $
            A_n := {y in X: abs(x - y) <= 1/n}
        $易知任意$A_n$非空，所以定义序列$(a_n)_(n=1)^oo$，由选择公理易知$forall a_n in X, abs(x - a_n) <= 1/n$

        任取$epsilon in RR^+$，存在$N >= ceil(1/epsilon)$，对于任意$n >= N$，就有
        $
            abs(x - a_n) <= 1/n <= 1/N <= epsilon
        $于是$(a_n)_(n=1)^oo$收敛到$x$

    2. $arrow.double.l$\
        如果存在这样的序列，那么说明
        $
            forall epsilon in RR^+, exists N >= 1, forall n >= N, abs(x - a_n) <= epsilon
        $这意味这对于任意$epsilon$，总能找到$a_n in X$，使得$abs(x - a_n) <= epsilon$成立，这正是$x in overline(X)$的定义
]

#definition[闭的(Closed)][
    $E subset.eq RR$，称$E$是闭的，当且仅当$E = overline(E)$
]

#corollary[使用序列定义闭的][
    $X subset.eq RR$，如果$X$是闭的，那么有收敛序列$(a_n)_(n=0)^oo subset.eq X$满足$lim_(n->oo)a_n in X$；

    同理，如果任意一个由$X$中元素组成的收敛序列，都收敛到$X$中，则$X$必然是闭的
]<corollary:lim-lang-for-closed>

#definition[极限点(Limit points)][
    + $X subset.eq RR$，称$x$是$X$的一个极限点/聚点，当且仅当$x in overline(X without {x})$

    + 称$x$是孤立点，当且仅当$x in X, exists epsilon in RR^+, forall y in X without{x}, abs(x - y) > epsilon$

]

#lemma[
    $a, b in RR, a < b$，$I$是区间$(a,b),[a,b],(a,b],[a,b), (a, oo),[a, +oo), (-oo, a), (-oo, a]$之一，那么任意$I$中元素都是$I$的极限点
]
#proof[
    只证明$I = [a, b]$的情况，任选$x in I$
    + 当$x = a$时，定义序列$(x + 1/n)_(n=N)^oo$，易知当$N>= 1/(b-a)$时
        $
            forall n >= N, a < x+1/n <= b =>forall n>= N, (x + 1/n) in I without {a}
        $且该序列收敛到$x$，那么由@lemma:lim-lang-for-closure 可知$x in overline(I without {a})$，所以$x = a$是$I$的一个极限点
    + 当$x = b$时，考虑序列$(x - 1/n)_(n=1)^oo$，同理$x = b$也是$I$的极限点
    + 当$a < x < b$时，可以同样使用序列$(a+1/n)_(n=N)^oo$，但是要调整$N$
]


#definition[有界集][
    $X subset.eq RR$被称作是有界集，当且仅当$exists M in RR^+, X subset.eq [-M, M]$；如果不存在这样的$M$，则称为无界集
]

#theorem[直线上的 Heine–Borel 定理][
    $X subset.eq RR$，下列两个命题是等价的
    + $X$是闭的、有界的
    + 给定实数序列$(a_n)_(n=0)^oo subset.eq X$，存在原序列的子序列$(a_(n_j))_(j=0)^oo$收敛到$L, L in X$
]<theorem:heine-borel-on-RR-line>

#problem[证明@lemma:closure-basic-property][见前]
#problem[证明@lemma:common-set-closure][见前]
#problem[试举一例：$X, Y subset.eq RR, overline(X inter Y) != overline(X) inter overline(Y)$]
#solution[
    取$X = [0, 1], Y =(1, 2]$就有
    $
                  overline(X inter Y) & = overline(emptyset) = emptyset \
        overline(X) inter overline(Y) & = [0, 1] inter [1, 2] = {1}
    $

]

#problem[证明@lemma:lim-lang-for-closure][见前]

#problem[$X subset.eq RR$，证明$overline(X)$是闭的.
    进一步的，证明任意包含$X$的闭集$Y$也包含$overline(X)$]
#proof[
    + 任选$x in overline(overline(X))$，那么就有
        $
            forall epsilon in RR^+, exists y in overline(X), abs(x - y) <= epsilon
        $由于$y in overline(X)$，那么就有
        $
            forall delta in RR^+, exists z in X, abs(y - z) <= delta
        $综上就有
        $
            abs(x - z) <= abs(x - y) + abs(y - z) <= epsilon + delta
        $由于$epsilon, delta$是任取的，这说明$x in overline(X)$，于是就有$overline(overline(X)) subset.eq overline(X)$，再由@lemma:closure-basic-property 易有$overline(X) subset.eq overline(overline(X))$，于是$overline(X) = overline(overline(X))$，也即$overline(X)$是闭的

    + 任选$x in overline(X)$，就有
        $
            forall epsilon in RR^+, exists y in X, abs(x - y) <= epsilon
        $由于$X subset.eq Y$，那么$y in Y$，这说明$x in overline(Y)$，所以$overline(X) subset.eq overline(Y)$，由于$Y$是闭的，那么$overline(Y) = Y$，所以$overline(X) subset.eq Y$
]

#problem[$X subset.eq RR$，集合$Y$满足$X subset.eq Y subset.eq overline(X)$，证明$overline(Y) = overline(X)$]
#proof[
    + 任选$x in overline(X)$，那么有
        $
            forall epsilon in RR^+, exists y in X, abs(x - y) <= epsilon
        $由于$X subset.eq Y$，那么$y in Y$，这说明$x in overline(Y)$，于是$overline(X) subset.eq overline(Y)$
    + 任选$x in overline(Y)$，就有
        $
            forall epsilon in RR^+, exists y in Y, abs(x - y) <= epsilon
        $由于$Y subset.eq overline(X)$，那么$y in overline(X)$，这说明$x in overline(overline(X)) = overline(X)$，于是$overline(Y) subset.eq overline(X)$
    + 综上$overline(Y) = overline(X)$
]

#problem[$n, i in ZZ^+, 1<=i<=n, X_i$是$RR$上的闭集，证明$union.big_(i=1)^n X_i$也是闭的]
#proof[
    由@lemma:closure-basic-property ，有限并的闭包是闭包的有限并，于是
    $
        overline(union.big_(i=1)^n X_i) = union.big_(i=1)^n overline(X_i)
    $由于$X_i$都是闭的，那么
    $
        union.big_(i=1)^n overline(X_i) = union.big_(i=1)^n X_i
    $综上有
    $
        overline(union.big_(i=1)^n X_i) = union.big_(i=1)^n X_i
    $所以闭集的有限并也是闭集
]

#problem[$I$非空(可能无限)，$forall alpha in I, X_alpha subset.eq RR$且是闭集，证明$inter.big_(alpha in I) X_alpha$也是闭集]
#proof[

    由于
    $
        forall alpha in I, inter.big_(alpha in I)X_alpha subset.eq X_alpha
    $所以由@lemma:closure-basic-property 就有
    $
        forall alpha in I, overline(inter.big_(alpha in I)X_alpha) subset.eq overline(X_alpha) => overline(inter.big_(alpha in I)X_alpha) subset.eq inter.big_(alpha in I) overline(X_alpha)
    $由于$X_alpha$均为闭集，那么
    $
        overline(inter.big_(alpha in I)X_alpha) subset.eq inter.big_(alpha in I) X_alpha
    $再由@lemma:closure-basic-property 有
    $
        inter.big_(alpha in I) X_alpha subset.eq overline(inter.big_(alpha in I) X_alpha)
    $

    综上，闭集的任意交也是闭集
]

#problem[$X subset.eq RR$，$overline(X)$中的任意元素都是$X$的极限点或孤立点，但不能同时是.
    反之，$X$的任意一个极限点或孤立点都在$overline(X)$中]
#proof[
    + 任选$x in overline(X)$
        - 如果$x in.not X$，由于$x in overline(X)$，那么
            $
                forall epsilon in RR^+, exists y in X, abs(x - y) <= epsilon
            $易知$y != x$，所以这说明$x in overline(X without {x})$，所以$x$是$X$的极限点，同时由于$x in.not X$，所以$x$一定不是孤立点
        - 如果$x in X$
            - 如果存在$epsilon in RR^+$，使得$forall y in X, abs(x - y) <= epsilon$，那么$y = x$，那么$forall y in X without {x}, abs(x - y) > epsilon$，这正是孤立点的定义.
                如果$x$同时也是极限点的话，说明存在$y' in X without {x}$，使得$abs(x - y') <= epsilon$，这显然矛盾，所以不可能是极限点
            - 如果不存在$epsilon in RR^+$，使得
                $
                    forall y in X, abs(x - y) <= epsilon
                $成立，说明$y != x$，结合$x in overline(X)$，就有
                $
                    forall epsilon in RR^+, exists y in X without {x}, abs(x - y) <=epsilon
                $这正是极限点的定义.
                如果$x$同时也是孤立点的话，则存在$epsilon in RR^+$，满足$forall y in X, abs(x -y) <= epsilon => x = y$，显然矛盾

    + 如果$x$是$X$的一个孤立点，由定义$x in X subset.eq overline(X)$，所以孤立点一定在闭包内，如果$x$是$X$的一个极限点，由定义$x in overline(X without {x}) subset.eq overline(X)$，所以极限点也一定在闭包内
]

#problem[$X subset.eq RR and X != emptyset$，$X$有界当且仅当$-oo < inf(X), sup(X) < +oo$]
#proof[
    + $=>$\
        如果$X$有界，那么$exists M in RR^+, X subset.eq [-M, M]$，这说明
        $
            & forall x in X, -M <= x <= M => -M <= sup(X) <= M \
            & forall x in X, M >= x >= -M => M >= inf(X) >= -M \
        $所以$-oo < inf(X), sup(X) < +oo$
    + $arrow.double.l$\
        如果$-oo < inf(X), sup(X) < +oo$，那么取$inf(X) = N, sup(X) = M$，由上下确界的定义
        $
            forall x in X, N <= x <= M
        $取$M' = max(abs(N), abs(M))$，易有
        $
            forall x in X, -M'<=x <= M'
        $于是确实存在$M' in RR^+$满足上式，所以$X$有界
]

#problem[$X subset.eq RR$是有界的，那么$overline(X)$也是有界的]
#proof[
    假设$overline(X)$不是有界的，那么$
        exists y in overline(X), forall r in RR^+, abs(y) > r
    $由于$y in overline(X)$，那么
    $
        forall epsilon in RR^+, exists z in X, abs(y - z) <= epsilon
    $由于$X$是有界的，那么
    $
        exists M in RR^+, forall x in X, abs(x) <= M
    $特别的，有
    $
        abs(z) <= M
    $所以有
    $
        abs(y - z) <= epsilon => abs(y) <= abs(y-z) + abs(z) <= epsilon + M
    $这和$abs(y)$大于任意正实数矛盾，所以$overline(X)$不可能不是有界的
]

#problem[证明有限个有界集合的并集仍然是有界的；举例说明对（不）可数无限个集合不成立]
#proof[

    + $n in NN, X_1,...,X_n subset.eq RR$且有界，接下来证明$union.big_(n=1)^N X_n$也有界

        对$N$进行归纳，当$N=1$时，$union.big_(n=1)^1 X_n = X_1$，$X_1$有界，$union.big_(n=1)^1 X_n$也有界；现在归纳性的假设在$N$时成立，证明$N+1$的情况.

        由归纳假设
        $
            exists M in RR^+, forall x in union.big_(n=1)^N X_n, abs(x) <= M
        $对于$union.big_(n=1)^(N+1) X_n = X_(N+1) union union.big_(n=1)^N X_n$，$X_(N+1)$有界，令界为$N$，取新的界为$M' = max(N, M)$，易知
        $
            forall x in union.big_(n=1)^(N+1) X_n, abs(x) <= M'
        $所以在$N+1$时也是有界的

    + 无穷个有界集合的并集不一定也有界，定义集合
        $
            n in NN, X_n := {x in RR: abs(x) <= n }
        $取无穷并集$X = union.big_(n=1)^oo X_n$，易知$forall n in NN, X_n subset.eq X_(n+1)$，假设$X$有界，那么
        $
            exists M in RR^+, forall x in X, abs(x) <= M
        $易知也存在一个正整数$M'$满足$M <= M'$；可是根据$X_n$的定义，有集合
        $
            X_(M' + 1) = {x in RR^+: abs(x) <= M' + 1} subset.eq X
        $该集合的界为$M' + 1 > M' >= M$，矛盾.
        所以无穷个有界集合的并集不一定也有界
    + 有些无穷有界集合的并集是有界的，比如定义集合
        $
            n in ZZ^+, X_n := {x in RR: abs(x) <= 1/n}
        $易知$X_1 supset.eq X_2 supset.eq ...$
        ，于是
        $
            union.big_(n=1)^oo X_n = X_1
        $显然有界

]

#tip-block[

    有界集的有限并一定是有界的；无穷并有时候有界，有时候没有界，这和集合有关系：那些“越来越大”的集合，每一次并集都把界给撑大；那些“越来越小”的集合，都生活在前面集合的内部，所以界大不过最大集合的界
]


#problem[证明@theorem:heine-borel-on-RR-line]
#proof[
    + $=>$\
        取序列$(a_n)_(n=0)^oo$，由于$X$是有界的，那么$(a_n)_(n=0)^oo$也是有界的，根据@thm:bolzano-Weierstrass 可知也一定存在子序列收敛到$L in RR$

        而且$X$是闭的，根据@corollary:lim-lang-for-closed 可知子序列可以收敛到$L in X$.

    + $arrow.double.l$\
        如果$X$无界，那么存在一个序列$(a_n)_(n=0)^oo subset.eq X, n->oo, a_n -> oo$，其子序列不可能收敛到任何实数，矛盾

        任取序列$(a_n)_(n=0)^oo subset.eq X$，假设$a_n -> x in RR$，由条件该序列有子序列收敛到$L in X$，但是整个序列都收敛到$x$，这说明$x = L in X$，根据@corollary:lim-lang-for-closed 可知$X$是闭的

        综上$X$有界且是闭的
]


#problem[证明任意$RR$的有限子集都是有界且闭的]
#proof[
    取$X subset.eq RR, \#(X) = n, n in NN$，对$n$进行归纳，当$n=1$时，$X = {x_0}, x_0 in RR$，易知常数序列$(x_0)_(n=0)^oo$收敛到$x_0 in X$，所以$X$是闭的，易知界为$abs(x_0) in RR^+$，所以是有界的

    归纳性的假设$\#(X) = N$时，$X$是闭的且有界，令界为$M$.

    现在证明$\#(X') = N+1$的情况，令$X' = X union {x'}, x' in.not X$，由于$X$是有界的，那么令$M' = max(M, abs(x')) in RR^+$，易知$M'$是$X'$的界，所以$X'$是有界的，由于闭集的有限并也是闭集，而$X, {x'}$都是闭集，那么$X' = X union {x'}$也是闭集，综上，实数的有限子集有界且为闭的
]


#problem[$E subset.eq RR$是一个非空有界集合，令$S := sup(E)$，证明$S in overline(E) and S in overline(RR without E)$]
#proof[

    由于$X$有界，那么$S = sup(E) in RR$，就有
    $
        forall n >= 1, exists e_n in E, S - 1/n < e_n <= S
    $定义序列$(e_n)_(n=0)^oo$，由夹逼定理易知$e_n -> S$，根据@lemma:lim-lang-for-closure 可知$S in overline(E)$

    定义序列$(S + 1/n)_(n=1)^oo$，易知
    $
        forall n >=1, (S+1/n) > S => forall n>=1, (S + 1/n) in RR without E
    $易知$(S+1/n) -> S$，所以再由@lemma:lim-lang-for-closure 可知$S in overline(RR without E)$
]

== 实值函数的代数

#definition[函数的限制][
    有函数$f:X->Y$，可以选取$X$的子集$X'$，如下定义新函数
    $
        f|_X'(x) = cases(f(x)\, &x in X', "undefined" \, &x in.not X')
    $函数$f|_X'$称为$f$在$X'$上的限制
]

#definition[函数代数运算][
    对于函数$f: X->RR, g:X->RR$，定义

    + 加法：$(f+g): X->RR, (f+g)(x) = f(x) + g(x)$
    + 减法：$(f-g): X->RR, (f-g)(x) = f(x) - g(x)$
    + 最大值：$max(f, g): X->RR, max(f, g)(x) = max(f(x), g(x))$
    + 最小值：$min(f, g): X->RR, min(f, g)(x) = min(f(x), g(x))$
    + 乘法：$(f g):X->RR, (f g)(x) = f(x)g(x)$
    + 除法：$(f\/g):X->RR, (f\/g)(x) = f(x)\/g(x), g(x) != 0$
    + 数乘：$c in RR, c f: X->RR, (c f)(x) = c f(x)$
]

#tip-block[
    + 数乘可以看作乘法的特例，考虑常数函数$g: X->RR, forall x in X, f(x) = c$，那么$(f g)(x) = f(x)g(x) = c f(x)$
    + 乘法和函数复合不是一种操作
]

#problem[$f:RR->RR, g:RR->RR, h:RR->RR$，下列等式哪些是对的，哪些是错的？
    给错的等式举一个反例
    + $(f + g) compose h = (f compose h) + (g compose h)$
    + $f compose (g + h) = (f compose g) + (f compose h)$
    + $(f + g) h = (f h) + (g h)$
    + $f (g + h) = (f g) + (f h)$
]
#solution[
    + 成立
        $
            forall x in X, ((f+g) compose h)(x) & = (f+g)(h(x)) = f(h(x)) + g(h(x)) \
            & = (f compose h)(x) + (g compose h)(x) = ((f compose h) + (g compose h))(x)
        $
    + 不成立，取$g(x) = -2x, h(x) = 2x，f(x) = x^2$，就有
        $
            (f compose (g + h))(x) = f((g+h)(x)) = f(g(x) + h(x)) = f(0) = 0
        $而
        $
            (f compose g)(x) = f(g(x)) = 4x^2\
            (f compose h)(x) = f(h(x)) = 4x^2\
        $显然不相等
    + 成立
        $
            ((f + g) h)(x) & = (f + g)(x) h(x) = (f(x) + g(x)) h(x) \
                           & = f(x) h(x) + g(x) h(x) \
                           & = (f h)(x) + (g h)(x) \
                           & = ((f h) + (g h))(x)
        $
    + 成立
        $
            (f (g + h))(x) & = f(x) (g + h)(x) = f(x) (g(x) + h(x)) \
                           & = f(x) g(x) + f(x) h(x) \
                           & = (f g)(x) + (f h)(x) \
                           & = ((f g) + (f h))(x)
        $
]
#tip-block[
    对于第二个式子，如果选取一个$f, g, h$都是线性的函数，则成立；这是因为复合运算不保加法，除非函数本身是线性的，否则一般不成立
]

== 函数的极限值

#definition[$epsilon$-接近性][
    $X subset.eq RR, f:X ->RR, L in RR, epsilon in RR^+$，称$f$是$epsilon$-接近于$L$的，当且仅当$forall x in X, abs(f(x) - L) <= epsilon$
]

#definition[局部$epsilon$-接近性][
    $X subset.eq RR, f: X->RR, L in RR, x_0 in overline(X), epsilon in RR^+$，称$f$在$x_0$处$epsilon$-接近于$L$，当且仅当存在$delta in RR^+$，使得$f$在${x in X: abs(x - x_0) < delta}$的限制上$epsilon$-接近于$L$
]

#definition[函数在一点收敛][
    $X subset.eq RR, f:X->RR, E subset.eq X, x_0 in overline(E), L in RR$，称$f$在$E$中沿$x_0$收敛到$L$，当且仅当$f$限制在$E without {x_0}$上时，对任意$epsilon in RR^+$，$f$都在$x_0$处$epsilon$-接近于$L$，记作
    $
        lim_(x -> x_0; x in E) f(x) = L
    $

    反之，则称$f$在$x_0$处发散.
]

#remark[上述定义的另一种说法][
    $
        lim_(x->x_0; x in E)f(x) = L \ <=> \ forall epsilon in RR^+, exists delta in RR^+, forall x in {x in E: 0 < abs(x - x_0) < delta}, abs(f(x) - L) <= epsilon
    $
]

#proposition[函数在一点收敛的另一种说法][
    $X subset.eq RR, f: X->RR, E subset.eq X, x_0 in overline(E), L in RR$，下列两命题等价
    + 极限命题：$f$在$E$中沿$x_0$收敛到$L$
    + 序列命题：$forall (a_n)_(n=0)^oo subset.eq E without {x_0} and lim_(n->oo)a_n = x_0 => lim_(n->oo)f(a_n) = L$
]<proposition:f-limit-on-point-2ways>
#proof[
    + $=>$\
        由于$f$在$E$中沿$x_0$收敛到$L$，那么就有
        $
            forall epsilon in RR^+, exists delta in RR^+, forall x in {x in E: 0< abs(x - x_0) < delta} => abs(f(x) - L) <= epsilon
        $由于任取了$(a_n)_(n=0)^oo subset.eq E without {x_0}$且有$a_n -> x_0$，说明对于一个$delta in RR^+$，有$N >= 0, forall n >= N, 0 < abs(a_n - x_0) < delta$，所以可以推出
        $
            abs(f(a_n) - L) <= epsilon
        $
    + $arrow.double.l$\
        假设序列命题成立，但是$f$在$E$中不沿着$x_0$收敛到$L$，那么
        $
            exists epsilon in RR^+, forall delta in RR^+, exists x in {x in E: 0< abs(x - x_0)<delta}, abs(f(x) - L) > epsilon
        $固定$epsilon$，对$n >= 1$，令$delta = 1/n$，那么存在$a_n in E$使得
        $
            0 < abs(a_n - x_0) < 1/n, abs(f(a_n) - L) > epsilon
        $由于假设，应该有$a_n -> x_0, f(a_n) -> L$，但实际上$f(a_n)$总是不能$epsilon$-接近于$L$，矛盾，所以$f$在$E$中沿$x_0$收敛到$L$
]

#corollary[函数在每个点至多有一个极限][
    $X subset.eq RR, E subset.eq X, x_0 in overline(E), f: X->RR, forall x_0 in E, f$在$x_0$处至多有一个极限
]
#proof[
    如果$f$在$x_0$处有两个极限$L, L'$，由于$x_0 in overline(E)$，那么根据@lemma:lim-lang-for-closure 可知有一个序列$(a_n)_(n=0)^oo subset.eq E$收敛到$x_0$，由于$L$是$f$在$E$中沿着$x_0$的极限，说明序列$(f(a_n))_(n=0)^oo$收敛到$L$，又因为$L'$也是$x_0$处的极限，所以序列$(f(a_n))_(n=0)^oo$也收敛到$L'$

    根据@thm:uniqueness-of-real-limit，只能是$L = L'$，也即函数在每个点至多有一个极限
]

#property[函数的极限法则][
    $X subset.eq RR, E subset.eq X, x_0 in overline(E), f: X->RR, g:X->RR$，考虑
    $
        lim_(x->x_0; x in E) f(x) = L, lim_(x->x_0; x in E)g(x) = M
    $那么有
    + $(f+g)$在上述条件下(之后省略)收敛到$L + M$
    + $f - g$收敛到$L - M$
    + $max(f, g)$收敛到$max(L, M)$
    + $min(f, g)$收敛到$min(L, M)$
    + $f g$收敛到$L M$
    + $c in RR, c f$收敛到$c L$
    + $M != 0$时，$f\/g$收敛到$L/M$
]<property:function-limit-law>
#proof[
    记$(a_n)_(n=0)^oo subset.eq E$且收敛到$x_0$，由于$f$和$g$在$E$中沿$x_0$分别收敛到$L$和$M$，那么序列$(f(a_n))_(n=0)^oo$和$(g(a_n))_(n=0)^oo$分别收敛到$L, M$

    + 序列$((f+g)(a_n))_(n=0)^oo$收敛到$lim_(n->oo)(f+g)(a_n) = lim_(n->oo)f(a_n) + lim_(n->oo)g(n) = L + M$
    + 剩下的内容可以按照实值函数的代数和@thm:limit-law 推出
]

#proposition[极限是局部的][
    $X subset.eq RR, E subset.eq X, x_0 in overline(E), f: X->RR, L in RR, delta in RR^+$，那么有
    $
        lim_(x->x_0;x in E)f(x) = L <=> lim_(x->x_0; x in E inter (x_0 - delta, x_0 + delta))f(x) = L
    $
]<proposition:limit-are-local>
#proof[
    定义集合$E' = E inter (x_0 - delta, x_0 + delta)$
    + $=>$\
        如果$lim_(x->x_0;x in E)f(x) = L$，那么说明
        $
            forall epsilon in RR^+, exists eta in RR^+, forall x in {x in E: 0 < abs(x - x_0) < eta}, abs(f(x) - L) <= epsilon
        $取$eta' = min(eta, delta)$，任意$x in {x in E': 0 < abs(x - x_0) < eta'}$，都有$abs(x - x_0) < eta' <= eta$，所以就有$abs(f(x) - L) <= epsilon$，这说明
        $
            lim_(x->x_0; x in E inter (x_0 - delta, x_0 + delta))f(x) = L
        $
    + $arrow.double.l$\
        如果$lim_(x->x_0;x in E') f(x) = L$，说明
        $
            forall epsilon in RR^+, exists eta in RR^+, forall x in {x in E': 0 < abs(x - x_0) < eta}, abs(f(x) - L) <= epsilon
        $令$eta' = min(eta, delta)$，那么$forall x in {x in E: 0< abs(x - x_0) < eta'}$都有$x < eta' < eta$，于是$abs(f(x) - L) <= epsilon$，所以有
        $
            lim_(x->x_0; x in E)f(x) = L
        $
]
#tip-block[
    如果函数在$x_0$处的极限存在，那么极限值和$x_0$附近相关，和远处的关系不大
]

#problem[证明@proposition:f-limit-on-point-2ways][见前]
#problem[证明@property:function-limit-law][见前]
#problem[证明@proposition:limit-are-local][见前]
#problem[$X subset.eq RR, E subset.eq X, x_0 in overline(E), f: X->RR, g: X->RR, h: X->RR$，满足$forall x in E, f(x) <= g(x) <= h(x)$，证明
    $
        lim_(x -> x_0; x in E)f(x) = lim_(x->x_0;x in E)h(x) = L => lim_(x->x_0;x in E)g(x) = L
    $
]
#proof[
    取序列$(a_n)_(n=0)^oo subset.eq E without {x_0}$，且$lim_(n->oo)a_n = x_0$，由于$f, g$都在$E$中沿$x_0$收敛到$L$，于是序列$(f(a_n))_(n=0)^oo$和序列$(h(a_n))_(n=0)^oo$收敛到$L$
    由于$forall x in E, f(x) <= g(x) <= h(x)$，那么
    $
        forall n >= 0, f(a_n) <= g(a_n) <= h(a_n)
    $根据@cor:squeeze-test 可知序列$(g(a_n))_(n=0)^oo$收敛到$L$，于是函数$g$在$E$中沿$x_0$收敛到$L$
]

== 连续函数








#pagebreak()
