#import "@preview/theorion:0.6.0": *
#import cosmos.fancy: *

= 级数

== 有限级数

#definition[有限级数][
    $m, n in ZZ$，$(a_i)_(i=m)^n$是一个有限实数序列，递归的定义有限级数为序列的有限和
    $
        & sum_(i=m)^n a_i := 0, n < m \
        & sum_(i=m)^(n+1) a_i := (sum_(i=m)^n a_i) + a_(n+1), n >= m- 1
    $
]

// #example[
//   $
//     sum_(i=m)^(m+1)a_i & = sum_(i=m)^m a_i + a_(m+1) \
//                        & = sum_(i=m)^(m-1) a_i + a_m + a_(m+1) \
//                        & = 0 + a_m + a_(m+1) = a_m + a_(m+1)
//   $
// ]
#note-block[
    如无特殊说明，都是实数级数
]

#property[有限级数的性质][
    + $m,n,p in ZZ and m <= n < p$，有
        $
            sum_(i=m)^n a_i + sum_(i=n+1)^p a_i = sum_(i=m)^p a_i
        $
    + $m,n,k in ZZ, m <= n$，有
        $
            sum_(i=m)^n a_i = sum_(j=m+k)^(n+k) a_(j-k)
        $
    + $m,n in ZZ, m <= n$，有
        $
            sum_(i=m)^n (a_i + b_i) = sum_(i=m)^n a_i + sum_(i=m)^n b_i
        $
    + $m,n in ZZ,m <=n, c in RR$，有
        $
            sum_(i=m)^n (c a_i) = c sum_(i=m)^n a_i
        $
    + (三角不等式) $m, n in ZZ, m <= n$，有
        $
            abs(sum_(i=m)^n a_i) <= sum_(i=m)^n abs(a_i)
        $
    + (比较定理) $m, n in ZZ, m <= n$，有
        $
            forall m <= i <= n, a_i <= b_i => sum_(i=m)^n a_i <=sum_(i=m)^n b_i
        $
]<prop:finite-series-algebra>

#pagebreak()

#definition[有限集上进行求和][
    $X$是有限集且$\#(X) = n in NN$，有函数$f:X -> RR$，以及双射函数$g: {i in NN: 1<=i<=n} -> X$，定义有限集上的求和为
    $
        sum_(x in X) f(x) := sum_(i=1)^n f(g(i))
    $
]
#remark[
    这里函数$g$的角色类似于取指函数，接受地址$i$，从$X$里取出值$x$，再作为参数放到$f$里
]
#proposition[有限集的和是良定义的][
    $X$是有限集且$\#(X) = n in NN$，$f:X -> RR$，$g:{i in NN: 1<=i <= n} -> X$和$h: {i in NN: 1<= i<= n} -> X$都是双射函数，那么
    $
        sum_(i=1)^n f(g(i)) = sum_(i=1)^n f(h(i))
    $
]
#proof[
    对$n$进行归纳，当$n = 0$时，由定义就有
    $
        sum_(i=1)^0 f(g(i)) = 0 = sum_(i=1)^0 f(h(i))
    $成立，现在归纳的假设$n$时成立，证明$n+1$的情况，令$x := g(n+1)$，由于$g$是双射，那么$x in X$，于是就有
    $
        sum_(i=1)^(n+1)f(g(i)) = sum_(i=1)^n f(g(i)) + f(x)
    $同时由于$h$也是双射，那么唯一存在$1 <= j<= n+1$，使得$x = h(j) = g(n+1)$，于是就有
    $
        sum_(i=1)^(n+1)f(h(i)) & = sum_(i=1)^j f(h(i)) + sum_(i = j+1)^(n+1)f(h(i)) \
        & = sum_(i=1)^(j-1)f(h(i)) + f(h(j)) + sum_(i = j+1)^(n+1)f(h(i)) \
        & = sum_(i=1)^(j-1) f(h(i)) + f(x) + sum_(i=j)^n f(h(i+1))
    $

    接下来定义函数$tilde(h):{i in NN: 1<=i<=n} -> X without {x}$为
    $ tilde(h)(i) = cases(h(i)&\, 1<= i<=j-1, h(i+1)&\, j<=i<=n) $于是就有
    $
        sum_(i=1)^(j-1)f(tilde(h)(i)) + f(x) + sum_(i=j)^(n)f(tilde(h)(i)) = sum_(i=1)^n f(tilde(h)(i)) + f(x)
    $根据归纳假设，此时的$tilde(h)$正是$n$时的双射函数，所以
    $ sum_(i=1)^n f(tilde(h)(i)) = sum_(i=1)^n f(g(i)) $于是
    $
        sum_(i=1)^(n+1) f(g(i)) & = sum_(i=1)^n f(g(i)) + f(x) \
                                & =sum_(i=1)^n f(tilde(h)(i)) + f(x) \
                                & =sum_(i=1)^(n+1) f(h(i))
    $成立
]
#remark[
    可以想象$f, g$代表了不同的求和顺序，对于有限集合上的求和来说，顺序并不关键
]

#property[有限集合上求和的性质][
    + $X = emptyset, f:X -> RR$，那么
        $
            sum_(x in X) f(x) = 0
        $
    + $X = {x_0}, f:X->RR$，那么
        $
            sum_(x in X)f(x) = f(x_0)
        $
    + $X$是有限集，$f:X -> RR, g:Y -> X$且$g$是双射，那么
        $
            sum_(x in X)f(x) = sum_(y in Y)f(g(y))
        $
    + $n, m in ZZ, n<=m, X = {i in ZZ: n<=i<=m}$，那么
        $
            sum_(i=n)^m a_i = sum_(i in X)a_i
        $
    + $X inter Y = emptyset, f: X union Y -> RR$，那么
        $
            sum_(x in X union Y)f(x) = sum_(x in X)f(x) + sum_(y in Y) f(y)
        $
    + $X$是有限集，$f, g: X -> RR$，那么
        $
            sum_(x in X)(f(x) + g(x)) = sum_(x in X)f(x) + sum_(x in X)g(x)
        $
    + $X$是有限集，$c in RR, f:X -> RR$，那么
        $
            sum_(x in X)c f(x) = c sum_(x in X)f(x)
        $
    + $X$是有限集，$f, g:X->RR$且$forall x in X, f(x) <= g(x)$，那么
        $
            sum_(x in X) f(x) <= sum_(x in X)g(x)
        $
    + $X$是有限集，$f:X -> RR$，那么
        $
            abs(sum_(x in X)f(x)) <= sum_(x in X)abs(f(x))
        $
]<prop:finite-func-sum-algebra>

#lemma[笛卡尔积集合上求和][
    $X, Y$是有限集，$f:X times Y -> RR$是一个函数，那么
    $
        sum_(x in X)(sum_(y in Y) f(x,y)) = sum_((x,y) in X times Y) f(x, y)
    $
]
#proof[
    令$X, Y$的基数分别为$n,m in NN$，对$n$进行归纳.
    当$n=0$时，$X =emptyset$，那么$X times Y = emptyset$，于是
    $
        sum_(x in X)(sum_(y in Y)f(x, y)) = sum_((x, y) in X times Y)f(x,y) = 0
    $现在归纳的假设$n$时成立，证明$n+1$的情况.

    那么$\#(X) = n+1$，令$X' := X without {x_0}$，易知$\#(X') = n$，于是就有
    $
        sum_(x in X)(sum_(y in Y) f(x, y)) & = sum_(x in X' union {x_0})(sum_(y in Y)f(x, y)) \
        & = sum_(x in X')(sum_(y in Y) f(x, y)) + sum_(x = x_0)(sum_(y in Y) f(x, y)) \
        & =sum_(x in X')(sum_(y in Y) f(x, y)) + sum_(y in Y)f(x_0, y) \
        & =sum_((x, y) in X' times Y)f(x, y) + sum_((x, y) in {x_0} times Y)f(x, y) \
        & = sum_((x, y) in X times Y)f(x, y)
    $
]

#corollary[有限级数的富比尼定理(Fubini’s theorem)][
    $X, Y$是有限集，令$f:X times Y -> RR$，那么就有
    $
        sum_(x in X)(sum_(y in Y)f(x, y)) & = sum_((x, y) in X times Y)f(x, y) \
                                          & = sum_((y, x) in Y times X)f(x, y) \
                                          & = sum_(y in Y)(sum_(x in X)f(x, y))
    $
]<coro:fubini-finite-series>
#proof[
    令函数$h:Y times X -> X times Y$为$h(y, x) = (x, y)$，现在证明这是双射

    $forall (y, x) in Y times X, h(y, x) = (x, y) in X times Y$，所以是满射的.

    $forall (x, y) in X times Y => x in X and y in Y$，那么$(y, x) in Y times X$，所以确实是存在的，接着证明唯一存在，假设有两组不同的$(x, y), (x', y')$满足$h(y, x) = (x, y), h(y', x') =(x', y') =(x, y)$，那么就有$x = x' and y = y'$，所以$(x, y) = (x', y')$，所以是单射，综上$h$是双射

    于是由@prop:finite-func-sum-algebra(3)就有
    $
        sum_((x, y) in X times Y)f(x, y) & = sum_((y, x) in Y times X)f(h(y, x)) = sum_((y, x) in Y times X)f(x, y) \
        & = sum_(y in Y)(sum_(x in X)f(x, y))
    $
]
#remark[
    Fubini定理保障了交换求和顺序的合法性(至少在有限集上)
]

#definition[有限乘积][
    $m, n in ZZ$，$(a_i)_(i=n)^m$是一个有限序列，递归的定义有限乘积为
    $
        & product_(i=m)^n a_i := 1, n < m \
        & product_(i=m)^(n+1) a_i := (product_(i=m)^(n)a_i) a_(n+1), n >= m-1 \
    $
]

#definition[有限集合上的乘积][
    $X$是一个有限集合，基数为$n$，$f:X -> RR$是函数，有双射函数$h:{i in NN:1<=i<=n} ->X$，定义有限集合上的乘积为
    $
        product_(x in X)f(x) = product_(i=1)^n f(h(i))
    $
]

#property[有限乘积的性质][
    + $m, n, p in ZZ， m<=n <p$，有
        $
            (product_(i=m)^n a_i) (product_(i=n+1)^p a_i) = product_(i=m)^p a_i
        $
    + $m,n,k in ZZ, m<=n$，有
        $
            product_(i=m)^n a_i = product_(i=m+k)^(n+k) a_(i-k)
        $
    + $m, n in ZZ, m<=n$，有
        $
            product_(i=m)^n (a_i b_i) = (product_(i=m)^n a_i)(product_(i=m)^n b_i)
        $
    + $m, n in ZZ, m<=n, c in RR$，有
        $
            product_(i=m)^n (c a_i) = c^(n-m+1)product_(i=m)^n a_i
        $
    + (三角不等式变成等式了)$m, n in ZZ, m<=n$，有
        $
            abs(product_(i=m)^n a_i) = product_(i=m)^n abs(a_i)
        $
    + 比较定理不再成立了
]

#property[有限集合乘积][
    + $X = emptyset, f:X ->RR$，有
        $
            product_(x in X)f(x) = 1
        $
    + $X = {x_0}, f:X -> RR$，有
        $
            product_(x in X) = f(x_0)
        $
    + $X$是有限集，$f:X -> RR, g:Y->X$，有
        $
            product_(x in X)f(x) = product_(y in Y)f(g(y))
        $
    + $n,m in ZZ,n <= m, X = {i in ZZ: n<=i<=m}$，有
        $
            product_(i=n)^m a_i = product_(i in X)a_i
        $
    + $X,Y$都是有限集且$X inter Y = emptyset, f:X union Y -> RR$，有
        $
            product_(z in X union Y)f(z) = (product_(x in X)f(x))(product_(y in Y)f(y))
        $
    + $X$是有限集，$f:X->RR, g:X->RR$，有
        $
            product_(x in X)(f(x)g(x)) = (product_(x in X)f(x))(product_(x in X)g(x))
        $
    + $X$是有限集，且基数为$n$，$c in RR, f:X -> RR$，有
        $
            product_(x in X)c f(x) = c^n product_(x in X)f(x)
        $
    + 单调性不再成立了
    + 三角不等式变等式了
]

#problem[证明@prop:finite-series-algebra]
#proof[
    + 对$p$进行归纳，当$p = n+1$时有
        $
            sum_(i=m)^n a_i + sum_(i=n+1)^(n+1) a_i = sum_(i=m)^n a_i + a_(n+1) = sum_(i=m)^(n+1)a_i = sum_(i=m)^(p)a_i
        $成立，现在归纳性的假设$p > n+1$时成立，证明$p+1$的情况
        $
            sum_(i=m)^n a_i + sum_(i=n+1)^(p+1) a_i & =sum_(i=m)^n a_i + sum_(i=n+1)^(p) a_i + a_(p+1) \
            & = sum_(i=m)^p a_i + a_(p+1) = sum_(i=m)^(p+1)a_i
        $成立，归纳结束
    + 对$n$归纳，当$n = m$时
        $
            sum_(i=m)^m a_i = a_m, sum_(j = m+k)^(m+k)a_(j-k) = a_m
        $成立，现在归纳的假设$n$时成立，证明$n+1$的情况
        $
            sum_(i=m)^(n+1) a_i & = sum_(i=m)^n a_i + a_(n+1) \
            & = sum_(j=m+k)^(n+k)a_(j-k) + a_(n+1) \
            & = sum_(j=m+k)^(n+k)a_(j-k) + a_(n+1+ k -k) = sum_(j=m+k)^(n+1+k) a_(j-k)
        $成立，归纳结束
    + 对$n$归纳，当$n = m$时有
        $
            sum_(i=m)^m (a_i + b_i) = a_m + b_m = sum_(i=m)^m a_i + sum_(i=m)^m b_i
        $现在归纳的假设$n$时成立，证明$n+1$的情况
        $
            sum_(i=m)^(n+1) (a_i + b_i) & = sum_(i=m)^n (a_i + b_i) + a_(n+1) + b_(n+1) \
            & = sum_(i=m)^n a_i + a_(n+1) + sum_(i=m)^n b_i + b_(n+1) \
            & = sum_(i=m)^(n+1)a_i + sum_(i=m)^(n+1)b_i
        $成立，归纳结束
    + 对$n$进行归纳，当$n = m$时
        $
            sum_(i=m)^m (c a_i) = c a_m = c sum_(i=m)^m a_i
        $成立，现在归纳的假设在$n$时成立，证明$n+1$的情况
        $
            sum_(i=m)^(n+1)(c a_i) & = sum_(i=m)^n (c a_i) + c a_(n+1) \
                                   & = c sum_(i=m)^n a_i + c a_(n+1) \
                                   & =c(sum_(i=m)^n a_i + a_(n+1)) \
                                   & = c sum_(i=m)^(n+1) a_i
        $成立，归纳结束
    + 对$n$进行归纳，当$n=m$时
        $
            abs(sum_(i=m)^m a_i) = abs(a_m) = sum_(i=m)^m abs(a_i)
        $成立，现在归纳的假设在$n$时成立，证明$n+1$的情况
        $
            abs(sum_(i=m)^(n+1) a_i) = abs(sum_(i=m)^n a_i + a_(n+1)) & <= abs(sum_(i=m)^n a_i) + abs(a_(n+1)) \
            & <= sum_(i=m)^n abs(a_i) + abs(a_(n+1)) = sum_(i=m)^(n+1) abs(a_i)
        $成立，归纳结束

    + 对$n$进行归纳，当$n = m$时
        $
            a_m <= b_m => a_m = sum_(i=m)^m a_i <= sum_(i=m)^m b_i = b_m
        $现在归纳的假设$n$时成立，证明$n+1$的情况
        $
            sum_(i=m)^(n)a_i <= sum_(i=m)^(n)b_i, a_(n+1) <= b_(n+1) & => sum_(i=m)^(n)a_i + a_(n+1) <= sum_(i=m)^(n)b_i + b_(n+1) \
            & => sum_(i=m)^(n+1) a_i <= sum_(i=m)^(n+1) b_i
        $成立，归纳结束
]
#remark[
    主要是使用归纳法，和平时从$0, 1$开始的归纳不太一样，这里的整数变量比较多，选定确值去归纳反而麻烦，所以往往利用级数求和的上限角标和下限角标的关系展开归纳，比如$n=m$时级数实际上就只有一个元素在求和，这对应的起始情况，之后的$n$时成立意味这现在有$n-m+1$个元素在求和，最后的$n+1$的情况则是$n-m+2$个元素在求和，通过角标的关系，将传统数学归纳法的递推过程转化成级数中参与求和的元素的数量
]

#problem[证明@prop:finite-func-sum-algebra]
#proof[
    + 定义双射函数$g:{i in NN: 1<=i<=0} = emptyset -> emptyset$，由定义
        $
            sum_(x in emptyset)f(x) = sum_(i=1)^0 f(g(i)) = 0
        $
    + 定义双射函数$g:{1} -> {x_0}$，于是由定义
        $
            sum_(x in {x_0})f(x) = sum_(i=1)^(1)f(g(i)) = f(g(1)) = f(x_0)
        $
    + 由于$X$是有限集，令其基数为$n in NN$，由于$g:Y -> X$是双射函数，那么说明$Y$和$X$有一样的基数$n$，所以有双射函数$u:{i in NN:1<=i<=n} -> Y$，所以$g compose u:{i in NN: 1<=i<=n} -> X$也是双射函数，再定义双射函数$h:{i in NN: 1<=i<=n} -> X$，就有
        $
            & sum_(y in Y)f(g(y)) = sum_(i=1)^n f(g(u(i))) = sum_(i=1)^n f((g compose u )(i)) \
            & sum_(x in X)f(x) = sum_(i=1)^n f(h(i))
        $先前已经证明有限集求和是良定义的，$h, g compose u$都是${i in NN: 1 <= i<=n} ->X$的双射函数，所以就有
        $
            sum_(x in X)f(x) = sum_(y in Y)f(g(y)
        $
    + 由于$X = {i in ZZ: n<=i<=m}$是有限集且基数为$m-n+1$，取双射函数$h:{i in NN:1 <= i <=m-n+1} ->X, h(i) =n+i-1$，于是就有
        $
            sum_(i in X)a_i & = sum_(i=1)^(m-n+1)a_(h(i))
                              = sum_(i=1)^(m-n+1)a_(n+i-1) \
                            & = sum_(i=n)^m a_(i+n-1 -n + 1) = sum_(i=n)^m a_i
        $
    + 由于$X, Y$都是有限集，令其基数分别为$m, n$，那么分别有双射函数$h:{i in NN: 1<=i<=m} -> X$和$w:{i in NN: 1<=i<=n} -> Y$，由于$X inter Y = emptyset$，那么$\#(X union Y) = m+n$，定义一个双射函数$mu:{i in NN:1 <= i<= m+n}-> X union Y$满足
        $
            mu(i) = cases(h(i)&\,1<= i<= m, w(i-m)&\, m+1 <= i<=m+n)
        $易知$mu$也是双射的，于是
        $
            sum_(z in X union Y) f(z) & = sum_(i=1)^(m+n)f(mu(i)) = sum_(i=1)^(m)f(mu(i)) + sum_(i=m+1)^(m+n)f(mu(i)) \
            & = sum_(i=1)^(m)f(h(i)) + sum_(i=m+1)^(m+n)f(w(i-m)) \
            & = sum_(i=1)^(m)f(h(i)) + sum_(i=1)^(n)f(w(i)) \
            & = sum_(x in X)f(x) + sum_(y in Y) f(y)
        $
    + $X$是有限集合，令$\#(X) = n in NN$，于是有双射函数$h:{i in NN:1<=i<=n} -> X$，于是有
        $
            sum_(x in X)(f(x) + g(x)) & = sum_(i=1)^n f(h(i)) + g(h(i)) \
                                      & = sum_(i=1)^n f(h(i)) + sum_(i=1)^n g(h(i)) \
                                      & = sum_(x in X)f(x) + sum_(x in X)g(x)
        $
    + $X$是有限集合，令$\#(X) = n in NN$，于是有双射函数$h:{i in NN:1<=i<=n} -> X$，于是有
        $
            sum_(x in X)c f(x) = sum_(i=1)^n c f(h(i))
            = c sum_(i=1)^n f(h(i))
            = c sum_(x in X)f(x)
        $
    + $X$是有限集合，令$\#(X) = n in NN$，于是有双射函数$h:{i in NN:1<=i<=n} -> X$，由于$forall x in X, f(x) <= g(x)$，那么$forall 1<=i<=n, f(h(i)) <= g(h(i))$，于是就有
        $
            sum_(x in X)f(x) = sum_(i=1)^n f(h(i)) <= sum_(i=1)^n g(h(i)) = sum_(x in X)g(x)
        $
    + $X$是有限集合，令$\#(X) = n in NN$，于是有双射函数$h:{i in NN:1<=i<=n} -> X$，于是就有
        $
            abs(sum_(x in X)f(x)) = abs(sum_(i=1)^n f(h(i))) <= sum_(i=1)^n abs(f(h(i))) = sum_(x in X)abs(f(x))
        $
]

#problem[
    仿照级数的定义，为$product_(i=1)^n a_i$和$product_(x in X)f(x)$给出形式化的定义，有限级数上的结果对有限乘积也是类似的吗？
]
#note-block[
    这个题目的解答作为补充写在了正文里，这里不做展开
]

#problem[
    $n in NN$，递归的定义阶乘为
    $ 0! := 1, (n+1)! := n!(n+1) $令$x, y in RR$，证明二项式定理
    $
        (x+y)^n = sum_(j=0)^n (n!)/(j!(n-j)!) x^j y^(n-j)
    $
]
#proof[
    对$n$归纳，当$n=0$时
    $
        & (x+y)^n = (x+y)^0 = 1 \
        & sum_(j=0)^n (n!)/(j!(n-j)!) x^j y^(n-j) = 0!/(0! 0!)x^0 y^(0-0) = 1
    $成立，现在归纳性的假设$n$时成立，证明$n+1$的情况
    $ (x+y)^(n+1) = (x+y)^n (x+y) $代入归纳假设就有
    $
        & "  "(sum_(j=0)^n (n!)/(j!(n-j)!) x^j y^(n-j))(x + y) \
        & = (sum_(j=0)^n (n!)/(j!(n-j)!) x^(j+1)y^(n-j)) + (sum_(j=0)^n (n!)/(j!(n-j)!) x^j y^(n+1-j)) \
        & = (sum_(j=0)^(n-1) (n!)/(j!(n-j)!) x^(j+1)y^(n-j)) + x^(n+1) + y^(n+1) + (sum_(j=1)^n (n!)/(j!(n-j)!) x^j y^(n+1-j)) \
    $对第二个括号内的式子改变求和角标就有
    $
        sum_(j=1)^n (n!)/(j!(n-j)!) x^j y^(n+1-j) = sum_(j=0)^(n-1) n!/((j+1)!(n-j-1)!)x^(j+1)y^(n-j)
    $代入，并提取公共部分就有
    $
        "原式"= x^(n+1) + y^(n+1) + sum_(j=0)^(n-1)((n!)/(j!(n-j)!) + n!/((j+1)!(n-j-1)!))x^(j+1)y^(n-j)
    $对括号内涉及阶乘的式子化简有
    $
        & "  "n!/(j!(n-j)!) + n!/((j+1)!(n-j-1)!) \
        & = ((j+1)n!)/((j+1)!(n-j)!) + (n!(n-j))/((j+1)!(n-j)!) \
        & = ((n+1)!)/((j+1)!(n-j)!)
    $
    代入回原式就有
    $
        "原式"= x^(n+1) + y^(n+1) + sum_(j=0)^(n-1)(((n+1)!)/((j+1)!(n-j)!)x^(j+1)y^(n-j))
    $特别的，有以下成立
    $
        x^(n+1) = ((n+1)!)/((n+1)!(n-n)!)x^(n+1)y^(n-n)\
        y^(n+1) = ((n+1)!)/((-1 + 1)!(n- (-1))!)x^(-1+1)y^(n - (-1))
    $于是就有
    $
        "原式" & =sum_(j=-1)^(n)((n+1)!)/((j+1)!(n-j)!)x^(j+1)y^(n-j) \
               & = sum_(j=0)^(n+1) ((n+1)!)/(j!(n+1-j)!)x^j y^(n+1-j)
    $成立，归纳结束
]
#remark[
    最好的方法是写出待证明的式子，然后去拼凑
]

#problem[$X$是一个有限集，$m in ZZ$，任意$x in X$，$(a_n (x))_(n=m)^infinity$都是一个收敛的实数序列，证明$(sum_(x in X)(a_n (x)))_(n=m)^infinity$也是收敛的，且$
        lim_(n -> infinity) sum_(x in X)a_n (x) = sum_(x in X) lim_(n->infinity)a_n (x)
    $]
#proof[
    由于$X$是一个有限集，对$\#(X)$进行归纳，当$\#(X) = 1$时，仅有一个元素$x' in X$，且$(a_n (x))_(n=m)^infinity$收敛，于是令$c = lim_(n->infinity)a_n (x'), c in RR$，此外还有$
        (sum_(x in X) a_n (x))_(n=m)^infinity = (a_n (x'))_(n=m)^infinity
    $显然是收敛的

    进一步的，有
    $
        lim_(n->infinity)sum_(x in X)a_n (x) = lim_(n->infinity) a_n (x') = c\
        sum_(x in X) lim_(n->infinity) a_n (x) = lim_(n->infinity) a_n (x') = c
    $
    是成立的.
    归纳性的假设在$\#(X) = n$时成立，现在证明$\#(X) = n+1$的情况

    令新有限集合$X' = X union {x_0}, x_0 in.not X, \#(X) = n$，由归纳假设，就有$(sum_(x in X) (a_n (x)))_(n=m)^infinity$是收敛的，令其极限为$d in RR$，此外由条件，$x_0 in X, (a_n (x_0))_(n=m)^infinity$是收敛的，令其极限为$c_0 in RR$，那么就有
    $
        (sum_(x in X') (a_n (x)))_(n=m)^infinity = (sum_(x in X) (a_n (x)))_(n=m)^infinity + (a_n (x_0))_(n=m)^infinity
    $两个收敛序列的和也是收敛的，进一步的有
    $
        lim_(n->infinity) sum_(x in X') a_n (x) = lim_(n->infinity) sum_(x in X) a_n (x) + lim_(n->infinity) a_n (x_0)\
        sum_(x in X') lim_(n->infinity) a_n (x) = sum_(x in X) lim_(n->infinity) a_n (x) + lim_(n->infinity) a_n (x_0)
    $由归纳假设有
    $
        lim_(n->infinity) sum_(x in X) a_n (x) = sum_(x in X) lim_(n->infinity) a_n (x)
    $代换并由极限运算可得
    $
        lim_(n -> infinity) sum_(x in X') a_n (x) = sum_(x in X') lim_(n->infinity)a_n (x)
    $归纳结束
]

#remark[
    有限个序列的和的极限 = 有限个序列的极限的和，但是扩展到无穷后会有若干问题
]

#problem[
    $I$是有限集合，$forall i in I, E_i$是有限集合，且$forall i, j in I, i != j, E_i inter E_j = emptyset$，$forall x in union.big_(i in I)E_i, f(x) in RR$，证明
    $
        sum_(x in union.big_(i in I)E_i) f(x) = sum_(i in I) sum_(x in E_i)f(x)
    $
]
#proof[
    由于$I$是有限集合，对$\#(I)$进行归纳，当$\#(I) = 1$时，有$union.big_(i in I)E_i = E'$，显然有二者相等
    $
        sum_(x in union.big_(i in I)E_i) f(x) & = sum_(x in E')f(x) \
               sum_(i in I)sum_(x in E_i)f(x) & = sum_(x in E')f(x)
    $

    归纳性的假设在$\#(I) = n$时成立，现在证明$\#(I) = n+1$的情况，令$I' = I union {i_0}, i_0 in.not I, \#(I) = n$，且$forall i, j in I', i!=j, E_i inter E_j = emptyset$于是有
    $
        sum_(x in union.big_(i in I')E_i)f(x) = sum_(x in (union.big_(i in I)E_i) union E_(i_0))f(x) = sum_(x in union.big_(i in I)E_i) f(x) + sum_(x in E_(i_0))f(x)\
        sum_(i in I') sum_(x in E_i) f(x) = sum_(i in I union {i_0}) sum_(x in E_i)f(x) = sum_(i in I) sum_(x in E_i) f(x) + sum_(x in E_(i_0))f(x)
    $由归纳假设有
    $
        sum_(x in union.big_(i in I)E_i) f(x) = sum_(i in I) sum_(x in E_i)f(x)
    $代入易知相等，归纳结束
]

#problem[
    $n, m in NN, forall 1<= i <= n, a_i in NN and a_i <= m$，那么有
    $
        sum_(i = 1)^m a_i = sum_(j=1)^m \#({1 <= i<= n: a_i >= j})
    $
]

#tip-block[
    这里要用双计数法进行证明，就是对同一个对象（这里就是一个集合）使用两种不同方法进行计数，由于计算的是同一个对象，那么计数结果必然相等，以此来建立等式

    举一个例子：在任意$n$个人中，认识奇数个人的人数一定是偶数
    - 计数方法1：每个人认识的次数加起来，得到“总认识次数”
    - 计数方法2：由于每一对互相认识的人贡献了两次（A认识B算一次，B认识A算一次），所以“总认识次数”一定是偶数，但命题要求了是认识奇数个人的人数，那么想要满足“总认识次数”为偶数的约束，认识奇数个人的人数一定得是偶数个
]

#proof[
    令$c_(i j) = cases(1\, j <= a_i, 0\, j > a_i)$，固定$i$就有
    $
        sum_(j = 1)^m c_(i j) = a_i
    $这是因为$j$从$1$增长到$m$，每比$a_i$大一次，则加一，否则加0，正好是$a_i$的值，接着再对$1 <= i <= n$求和就有
    $
        sum_(i = 1)^n sum_(j = 1)^m c_(i j) = sum_(i = 1)^n a_i
    $
    接下来固定$j$，对$i$求和，显然有
    $
        sum_(i = 1)^n c_(i j) = \#(1 <= i <= n: a_i >= j)
    $这是因为此时相当于是统计大于$j$的$a_i$的个数，对其从$1 <= j <= m$求和就有
    $
        sum_(j = 1)^m sum_(i = 1)^n c_(i j) = sum_(j = 1)^m \#{1 <= i <= n: a_i >= j}
    $由@coro:fubini-finite-series 就有
    $
        &"    " sum_(i = 1)^n sum_(j = 1)^m c_(i j) = sum_(j = 1)^m sum_(i = 1)^n c_(i j) \
        & => sum_(i = 1)^n a_i = sum_(j = 1)^m \#{1 <= i <= n: a_i >= j}
    $

]

== 无穷级数

#definition[形式无穷级数][
    形式无穷级数是如下的表达式
    $
        sum_(n = m)^infinity a_n
    $
    其中$m, n in ZZ, n>= m, a_n in RR$
]
#note-block[
    这里“形式”的意思和以前的形式减法、形式除法和形式极限是一样的，在对无穷级数进行了严格定义后，将会使用正式的无穷级数记号
]

#definition[形式无穷级数的收敛][
    $sum_(n=m)^infinity a_n$是一个形式无穷级数，对于任意$N >= m$，定义前$N$项部分和为$
        S_N := sum_(n = m)^N a_n
    $其中$S_N in RR$，是一个有限级数，再定义无穷实数序列$(S_N)_(N = m)^infinity$，称形式无穷级数$sum_(n = m)^infinity a_n$是收敛的，当且仅当序列$(S_N)_(N=m)^infinity$是收敛的，进一步的有
    $
        sum_(n = m)^infinity a_n = lim_(N->infinity)S_N = L in RR
    $$L$称作该形式无穷级数的和.

    反之，如果$(S_N)_(N= m)^infinity$发散，则称该形式无穷级数发散，因此也不会给该无穷级数的和赋予任何实数
]

#lemma[形式无穷级数收敛性的判断][
    $sum_(n = m)^infinity a_n$是一个无穷实数级数，那么该无穷级数收敛当且仅当
    $
        forall epsilon in RR^+, exists N >=m, forall p, q >= N, abs(sum_(n=p)^q a_n) <= epsilon
    $
]<lem:test-foraml-infinite-series-convergent>
#proof[
    - $=>$\
        由定义，$(S_N)_(N= m)^infinity$收敛，即
        $
            forall epsilon in RR^+, exists N' >=m, forall p, q >= N', abs(S_p - S_q) <= epsilon
        $不妨令$p <= q$，化简绝对值项有
        $
            abs(S_p - S_q) & = abs(sum_(n=m)^p a_n - sum_(n=m)^q a_n) \
                           & = abs(sum_(n=m)^p a_n - (sum_(n=m)^p a_n + sum_(n=p+1)^q a_n)) \
                           & = abs(sum_(n = p+1)^q a_n)
        $由于$q >= p$，那么$q > p+1$，令$p' = p+1$，易知$p' > N'$，所以就有
        $
            abs(sum_(n = p')^q a_n) <= epsilon
        $这正是结论
    - $arrow.l.double$\
        反之同理，只需要将一个级数写作两个级数的差即可
        $
            abs(sum_(n= p)^q a_n) = abs(sum_(n=m)^q a_n - sum_(n=m)^(p-1) a_n)
        $
]

#corollary[无穷级数的零测试][
    $sum_(n=m)^infinity a_n$是一个收敛的无穷级数，那么$lim_(n->infinity)a_n = 0$
]<coro:zero-test-infinite-series>
#proof[
    由于该级数收敛，那么由@lem:test-foraml-infinite-series-convergent 就有
    $
        forall epsilon in RR^+, exists N >= m, forall p, q >= N, abs(sum_(n=p)^q a_n) <= epsilon
    $由于任意大于等于$N$的$p, q$都满足上式，自然在$p = q = n' >=N$时也满足，于是就有
    $
        abs(sum_(n=p)^q a_n) = abs(a_(n')) = abs(a_(n') - 0) <= epsilon
    $这正是$(a_n)_(n=m)^infinity$收敛到$0$的定义
]
#note-block[
    这个引理的逆命题是不成立的，比如$sum_(n=1)^infinity 1/n$，$(1/n)_(n=1)^infinity$收敛到$0$，但是级数是不收敛的
]

#definition[绝对收敛][
    $sum_(n=m)^infinity a_n$是形式实数级数，称其为绝对收敛的，当且仅当$sum_(n=m)^infinity abs(a_n)$是收敛的
]

#lemma[绝对收敛测试][
    $sum_(n=m)^infinity a_n$是无穷级数，如果该级数绝对收敛，那么也一定是收敛的；进一步的有不等式成立：
    $
        abs(sum_(n=m)^infinity a_n) <= sum_(n=m)^infinity abs(a_n)
    $
]<lem:test-absolute-convergent>

#proof[

    1. 由于$sum_(n=m)^infinity a_n$绝对收敛，就有
    $
        forall epsilon in RR^+, exists N >= m, forall p, q >= N, abs(sum_(n=p)^q abs(a_n)) <= epsilon
    $接着由@prop:finite-series-algebra 就有
    $
        abs(sum_(n=p)^q a_n) <= sum_(n=p)^q abs(a_n) = abs(sum_(n=p)^q abs(a_n)) <= epsilon
    $这正是无穷级数收敛的定义，所以无穷级数绝对收敛也一定收敛

    2. 令$S_N = sum_(n=m)^N abs(a_n), S'_N = abs(sum_(n=m)^N a_n)$，由@prop:finite-series-algebra 就有
        $
            forall N >= m, S_N >= S'_N
        $由(1)，这两个极限都是存在的，那么由极限的保序性就有
        $
            lim_(N->infinity)S_N = sum_(n=m)^infinity abs(a_n) >= abs(sum_(n=m)^infinity a_n) = lim_(N->infinity)S'_N
        $

]

#lemma[交错级数测试][
    $(a_n)_(n=m)^infinity$是一个非负、单调递减的实数序列，那么无穷级数$sum_(n=m)^infinity (-1)^n a_n$收敛，当且仅当$lim_(n->infinity)a_n = 0$
]
#proof[
    + $=>$\
        由@coro:zero-test-infinite-series，序列$((-1)^n a_n)_(n=m)^infinity$收敛到$0$，所以$(a_n)_(n=m)^infinity$也收敛到$0$
    + $arrow.double.l$\
        如果$(a_n)_(n=m)^infinity$收敛到$0$，令$S_N$为前$N$项部分和，于是$forall N >= m$有
        $
            S_(N+2) & = S_N + (-1)^(N+1)a_(N+1) + (-1)^(N+2)a_(N+2) \
                    & = S_N + (-1)^(N+1) (a_(N+1) - a_(N+2))
        $由于$(a_n)_(n=m)^infinity$非负且单调递减，那么$a_(N+1) - a_(N+2) >= 0$，于是$N$为奇数时，$S_(N+2) >= S_N$；$N$为偶数时，$S_(N+2) <= S_N$

        固定$N$是偶数，首先证明$forall k in NN, S_(N + 2k) <= S_N$，当$k = 0$时显然成立，现在归纳性的假设$k$时成立，证明$k+1$的情况
        $
            S_(N+2(k + 1)) & = S_(N+2k) + (-1)^(N+2k+1)a_(N+2k+1) + (-1)^(N+2k+2)a_(N+2k+2) \
                           & = S_(N+2k) + a_(N+2k+2) - a_(N+2k+1) \
                           & => S_(N+2(k+1)) - S_(N+2k) = a_(N+2k+2) - a_(N+2k+1)
        $由于$(a_N)_(N=m)^infinity$单调递减，所以$S_(N+2(k+1)) - S_(N+2k) = a_(N+2k+2) - a_(N+2k+1) <= 0$，所以有$S_(N+2(k+1)) <= S_(N+2k) <= S_N$，归纳结束


        接着证明$forall k in NN, S_(N+2k+1) >=S_(N+1)$，当$k=0$时显然成立，现在归纳性的假设$k$时成立，证明$k+1$的情况
        $
            S_(N + 2(k+1) + 1) = S_(N+2k+3) = S_(N+2k+1) + a_(N+2k+2) - a_(N+2k+3)
        $由于序列$(a_n)_(n=m)^infinity$单调递减，那么$a_(N+2k+2) - a_(N+2k+3) >= 0$，再由归纳假设就有$S_(N+2(k+1)+1) >= S_(N+2k+1) >= S_(N+1)$，归纳完毕

        此外，易有$S_(N+2k+1) = S_(N+2k) - a_(N+2k+1) <= S_(N+2k)$，综上就有
        $
            S_N - a_(N+1) = S_(N+1) <= S_(N+2k+1) <= S_(N+2k) <= S_N
        $
        那么$forall n >= N$，如果$n$是偶数，那么令$n = N + 2k$，于是就有
        $
            S_N - a_(N+1) <= S_n = S_(N+2k) <= S_N
        $如果$n$是奇数，令$n = N+2k+1$，于是就有
        $
            S_N - a_(N+1) <= S_n = S_(N+2k+1) <= S_N
        $这个结果说明
        $
            forall n>=N, -a_(N+1) <= S_n - S_N <= 0 => abs(S_n - S_N) <=a_(N+1)
        $
        由于$(a_n)_(n=m)^infinity$收敛到$0$，那么有
        $
            forall epsilon in RR^+, exists N' >=m, forall n >= N', abs(a_n - 0) = abs(a_n) <= epsilon
        $于是对于给定$epsilon$，选偶数$N >=N'$，任意$p, q >= N$就有
        $
            abs(S_p - S_q) <= abs(S_p - S_N) + abs(S_N + S_q) <= 2a_(N+1) <= 2epsilon
        $这说明$(S_N)_(N=m)^infinity$是柯西序列，因此该序列收敛，进一步的$sum_(n=m)^infinity (-1)^n a_n$收敛
]
#remark[
    麻烦之处在于固定偶数$N$后，对$S_n$进行夹逼
]

#property[无穷级数定律][
    $sum_(n=m)^infinity a_n, sum_(n=m)^infinity b_n$分别收敛到$x, y in RR$，$c in RR$，有以下成立
    + $sum_(n=m)^infinity (a_n + b_n) = sum_(n=m)^infinity a_n + sum_(n=m)^infinity b_n = x + y$

    + $sum_(n=m)^infinity c a_n = c sum_(n=m)^infinity a_n = c x$

    + $k in NN$，如果$sum_(n=m)^infinity a_n$和$sum_(n=m+k)^infinity a_n$其一收敛，那么另一个也收敛，且有恒等式$
            sum_(n=m)^infinity a_n = sum_(n=m)^(m+k-1) a_n + sum_(n=m+k)^infinity a_n
        $
    + $k in ZZ$，那么$sum_(n=m+k)^infinity a_(n-k) = sum_(n=m)^infinity a_n$
]<prop:infinitie-series-law>

#corollary[Telescoping 级数][
    $(a_n)_(n=0)^infinity$是收敛到$0$的实数序列，那么无穷级数$sum_(n=0)^infinity (a_n - a_(n+1))$收敛到$a_0$
]<coro:telescoping-series>

#problem[
    无穷级数$sum_(n=1)^infinity (-1)^n$是否收敛？
]
#proof[
    易知序列$((-1)^n)_(n=1)^infinity$不收敛，那么由@coro:zero-test-infinite-series 的逆否，该级数一定不收敛
]
#problem[证明@lem:test-foraml-infinite-series-convergent][见前证明]
#problem[证明@coro:zero-test-infinite-series][见前证明]
#problem[证明@lem:test-absolute-convergent][见前证明]
#problem[证明@prop:infinitie-series-law]
#proof[
    令$S_N, T_N$分别是$sum_(n=m)^infinity a_n, sum_(n=m)^infinity b_n$的前$N$项和
    + 令$sum_(n=m)^infinity (a_n + b_n)$的前$N$项和为$B_N$，那么就有
        $
            B_N = sum_(n=m)^N (a_n + b_n) = sum_(n=m)^N a_n + sum_(n=m)^N b_n = S_N + T_N
        $由于$(S_N)_(N=m)^infinity$和$(T_N)_(N=m)^infinity$都收敛，那么$(S_N+T_N)_(N=m)^infinity$也是收敛的，那么就有
        $
            sum_(n=m)^infinity (a_n + b_n) & = lim_(N->infinity) B_N \
            & = lim_(N->infinity) (S_N + T_N) \
            & = lim_(N->infinity)S_N + lim_(N->infinity)T_N \
            & = sum_(n=m)^infinity a_n + sum_(n=m)^infinity b_n = x + y
        $
    + 由于$(S_N)_(N=m)^infinity$是收敛的，那么$(c S_N)_(N=m)^infinity$也是收敛的，于是就有
        $
            sum_(n=m)^infinity (c a_n) = lim_(N->infinity) (c S_N) = c lim_(N->infinity)S_N = c x
        $
    + 取$k in NN$，对于两个序列$(S_N)_(N=m)^infinity$和$(S_N)_(N=m+k)^infinity$，其收敛与否与序列起始元素无关，所以其一收敛则另一个必收敛，于是就有
        $
            & S_N = sum_(n=m)^(m+k-1)a_n + sum_(n=m+k)^N a_n \
            & => lim_(N->infinity) S_N = sum_(n=m)^(m+k-1)a_n + lim_(N->infinity)S_N^(m+k) \
            & => sum_(n=m)^infinity a_n = sum_(n=m)^(m+k-1)a_n + sum_(n=m+k)^infinity a_n
        $其中$S_(N)^(m+k)$为从$m+k$项开始到第$N$项的和
    + $S_N$为$sum_(n=m)^infinity a_n$的前$N$项和，记$sum_(n=m+k)^infinity a_(n-k)$的前$N$项和为$
            T_N := sum_(n=m+k)^N a_(m-k), (N >= m+k)
        $令$j = n-k$，于是就有$
            T_N = sum_(j=m)^(N-k)a_j = S_(N-k)
        $由于$N>= m+k => N-k>=m$，所以$T_N$也是$(S_N)_(N=m)^infinity$中的一项，令$M=N-k$，因此
        $
            lim_(N->infinity)S_N = lim_(M->infinity)S_M = x
        $
]

#problem[证明@coro:telescoping-series]
#proof[
    假设$sum_(n=0)^infinity (a_n - a_(n+1))$的前$N$项和为$S_N = a_0-a_(N+1)$，使用归纳法进行证明，当$N = 0$时，$S_0 = sum_(n=0)^0 (a_n - a_(n+1)) = a_0 - a_1$，成立，现在归纳性的假设$N$时成立，证明$N+1$的情况
    $
        S_(N+1) & = S_N + (a_(N+1) - a_(N+2)) \
                & = a_0 - a_(N+1) + a_(N+1) - a_(N+2) = a_0 + a_(N+2)
    $成立，归纳结束.

    由于$(a_n)_(n=0)^infinity$收敛到$0$，于是$(a_0 + a_n)_(n=0)^infinity$也收敛，所以
    $
        sum_(n=0)^infinity (a_n - a_(n+1)) = lim_(N->infinity)S_N = lim_(N->infinity)(a_0 - a_(N+1)) = a_0 - 0 = a_0
    $
    如果$(a_n)_(n=0)^infinity$收敛到$L != 0$，也有
    $
        sum_(n=0)^infinity (a_n - a_(n+1)) = a_0 - L
    $

]

== 非负数的和

#proposition[$sum_(n=0)^infinity a_n$是非负无穷级数，那么该级数收敛当且仅当存在实数$M$，满足
    $
        sum_(n=m)^N a_n <= M, forall N >= n
    $
]
#proof[
    由于是非负级数，那么$forall N >=m, S_(N+1) - S_N = a_(N+1) >= 0$，所以$(S_N)_(N=m)^infinity$是单调递增的，单调递增有界必收敛，所以$(S_N)_(N=m)^infinity$一定有界
]

#corollary[比较测试][
    $sum_(n=m)^infinity a_n, sum_(n=m)^infinity b_n$是两个无穷级数，$abs(a_n) <= b_n ,forall n >=m$，如果$sum_(n=m)^infinity b_n$收敛，那么$sum_(n=m)^infinity a_n$绝对收敛，并且有
    $
        abs(sum_(n=m)^infinity a_n) <= sum_(n=m)^infinity abs(a_n) <= sum_(n=m)^infinity b_n
    $
]<coro:comparison-test>
#proof[
    令$T_N = sum_(n=m)^N abs(a_n), S_N = sum_(n=m)^infinity b_n$，由于$forall n>=m, b_n >= abs(a_n) >= 0$所以有
    $
        T_N <= S_N, forall N >= m
    $
    由于$sum_(n=m)^infinity b_n$是一个收敛的非负级数那么一定有上界$M$
    $
        T_N <= S_N <= M, forall N >= m
    $由于$sum_(n=m)^infinity abs(a_n)$也是一个非负级数且有上界$M$，那么$sum_(n=m)^infinity abs(a_n)$一定收敛，也就说明$sum_(n=m)^infinity a_n$绝对收敛，于是根据极限的保序性就有
    $
        & lim_(N->infinity) T_N <= lim_(N->infinity) S_N \
        & => sum_(n=m)^infinity abs(a_n) <= sum_(n=m)^infinity b_n
    $进一步的由@lem:test-absolute-convergent 就有
    $
        abs(sum_(n=m)^infinity a_n) <= sum_(n=m)^infinity abs(a_n) <= sum_(n=m)^infinity b_n
    $
]
#remark[
    由逆否就有：$abs(a_n) <= b_n, forall n>= m$，如果$sum_(n=m)^infinity a_n$不绝对收敛，那么$sum_(n=m)^infinity b_n$一定不收敛
]

#lemma[几何级数][
    $x in RR$，如果$abs(x) >= 1$，那么无穷级数$sum_(n=0)^infinity x^n$发散；如果$abs(x) < 1$，那么该级数绝对收敛并且有
    $
        sum_(n=0)^infinity x^n = 1/(1 - x)
    $
]<lem:geometry-series>
#proof[
    由@coro:zero-test-infinite-series 的逆否命题可知，如果级数求和序列的极限不为$0$或不收敛，则级数也不收敛，由@lem:x-n-power-limit-depend-x 可知，对于序列$(x^n)_(n=0)^infinity$，如果$abs(x) > 1$则发散，如果$x = 1$则收敛到$1$，如果$x = -1$则发散，所以只有在$abs(x) < 1$时序列$(x^n)_(n=0)^infinity$收敛，进而$sum_(n=0)^infinity x^n$收敛，接下来证明在$abs(x) < 1$时的级数

    假设该级数的前$N$项和为
    $
        S_N = (1 - x^(N+1))/(1-x)
    $使用数学归纳法证明，当$N = 0$时
    $
        S_0 = (1-x^(0+1))/(1-x) = 1 = sum_(n=0)^0 x^n
    $成立，现在归纳性的假设在$N$时成立，证明$N+1$的情况
    $
        S_(N+1) = S_N + x^(N+1) = (1-x^(N+1))/(1-x) + x^(N+1) = (1-x^(N+2))/(1-x)
    $成立，归纳结束

    前已证级数$sum_(n=0)^infinity x^n$在$abs(x) < 1$时收敛，那么就有
    $
        sum_(n=0)^infinity x^n & = lim_(N->infinity) (1-x^(N+1))/(1-x) \
                               & = 1/(1-x) - 1/(1-x) lim_(N->infinity)x^(N+1) \
                               & = 1/(1-x) - 1/(1 -x) 0 \
                               & = 1/(1-x)
    $这里使用了$abs(x) < 1$时，$n->infinity, x^n -> 0$
]

#proposition[柯西准则][
    令$(a_n)_(n=1)^infinity$是递减非负实数序列，那么级数$sum_(n=1)^infinity a_n$收敛，当且仅当级数
    $
        sum_(k=0)^infinity 2^k a_(2^k) = a_1 + 2a_2 + 4a_4 + ...
    $
    收敛
]

#proof[
    令$S_N = sum_(n=1)^N a_n, T_K = sum_(k=0)^K 2^K a_(2^K)$，由题述易知都是非负级数，那么只需证明$sum_(n=1)^infinity a_n$有界当且仅当$sum_(k=0)^infinity 2^k a_(2^k)$有界

    但是先需证明$forall K in NN, S_(2^(K+1) - 1) <= T_K <= 2S_(2^K)$，使用数学归纳法，当$K=0$时
    $
        S_(2^(0+1) - 1) & =S_1 = a_1 \
                    T_0 & = a_1 \
               2S_(2^0) & = 2S_1 = 2a_1
    $由于$(a_n)_(n=1)^infinity$是递减非负序列，那么就有$a_1 <= a_1 <= 2a_1$，成立，现在归纳性的假设$K$时成立，证明$K+1$的情况
    $
        T_(K+1) & = T_K + 2^(K+1)a_(2^(K+1))
    $此外$forall 2^(K+1) >= n >= 2^K + 1, a_n >= a_(2^(K + 1))$，那么就有
    $
        S_(2^K +1) = S_(2^K) + sum_(n=2^K + 1)^(2^(K+1)) a_n >= S_(2^K) + sum_(n=2^K + 1)^(2^(K+1)) a_(2^(K + 1)) &= S_(2^K) + (2^(K+1) - (2^K + 1) + 1)a_(2^(K + 1))\
        &= S_(2^K) + 2^K a_(2^(K + 1))
    $值得注意的是，上式中的$sum_(n = 2^K + 1)^(2^(K+1))a_(2^K + 1)$共有$2^K$个$a_(2^K + 1)$求和.
    于是就有
    $
        2S_(2^(K+1)) >= 2S_(2^K) + 2^(K+1)a_(2^(K+1))
    $另外一边，$forall n >= 2^(K+1), a_n <= a_(2^(K+1))$同理有
    $
        S_(2^(K+2) - 1) & = S_(2^(K+1) - 1) + sum_(n=2^(K+1))^(2^(K+2) - 1) a_n \
                        & <= S_(2^(K+1) - 1) + sum_(n = 2^(K+1))^(2^(K+2)-1)a_(2^(K+1)) \
                        & = S_(2^(K+1) - 1) + 2^(K+1) a_(2^(K+1))
    $综上，结合归纳假设
    $
        S_(2^(K+1) - 1) <= T_K <= 2S_(2^(K + 1))
    $就有
    $
        S_(2^(K+2) - 1) <= T_(K+1) <= 2S_(2^(K+1))
    $归纳结束

    于是可以看到，如果$(S_N)_(N=1)^infinity$有界，那么$(T_K)_(K=0)^infinity$也一定有界，如果$(T_K)_(K=0)^infinity$有界，那么$S_(2^(K+1) - 1)$也是有界的，进而$(S_N)_(N=1)^infinity$也是有界的
]

#corollary[超调和级数的收敛性][
    $q in RR^+$，无穷级数$sum_(n=1)^infinity 1/n^q$在$q > 1$时收敛，在$q <= 1$时发散
]<coro:hyperharmonic-convergent>
#proof[
    序列$(1/n^q)_(n=1)^infinity$是一个非负且递减的序列，那么$sum_(n=1)^infinity 1/n^q$收敛当且仅当$sum_(n=0)^infinity 2^k 1/((2^k)""^q) = sum_(k=0)^infinity 2^((1-q))""^k$收敛，对于这个几何级数，它收敛当且仅当$abs(2^(1-q)) < 1$，那么就有
    $
        0<2^(1-q) < 2^0 => 1-q < 0 => q > 1
    $
    于是在$q > 1$时收敛，在$0 < q <= 1$时发散
]

#problem[证明@coro:comparison-test][见前]
#problem[证明@lem:geometry-series][见前]
#problem[$sum_(n=0)^infinity a_n$是绝对收敛的实数级数，且满足$sum_(n=0)^infinity abs(a_n) = 0$，证明$forall n in NN, a_n = 0$]
#proof[
    假设存在$k in NN, a_k != 0$，那么对于该级数就有
    $
        sum_(n=0)^infinity abs(a_n) = sum_(n=0)^(k-1) abs(a_n) + abs(a_k) + sum_(n=k+1)^infinity abs(a_n) = 0
    $于是就有
    $
        sum_(n=0)^(k-1) abs(a_n) + sum_(n=k+1)^infinity abs(a_n) = -abs(a_k) < 0
    $显然矛盾，于是不存在$k in NN$使得$a_k != 0$，也即$forall k in NN, a_k = 0$
]

== 级数的重排
#proposition[非负级数重排不改变值][$sum_(n=0)^infinity a_n$是一个非负的收敛无穷级数，$f: NN->NN$是双射，那么级数$sum_(m=0)^infinity a_(f(m))$也是收敛的，而且有
    $
        sum_(n=0)^infinity a_n = sum_(m=0)^infinity a_(f(m))
    $
]<propositon:non-neg-series-rearrangment>
#proof[
    级数$sum_(n=0)^infinity a_n$收敛，记其级数为$S$，令其部分和为$S_N := sum_(n = 0)^N a_n$，由于$a_n >= 0$，那么$S_N$单调递增且有上界$S$

    任选$M in NN$，重排部分和为$T_M = sum_(m=0)^M a_(f(m))$，由于$f:NN->NN$是双射，那么$Y := {f(m): m<=M} subset.eq NN$是一个有限集合，于是$exists N in NN, forall m <= M, f(m) <=N$，令集合$X = {n in NN : n<= N}$，易有$Y subset.eq X$
    $
        T_M = sum_(m in Y) a_(m) <= sum_(n in X) a_n <= S
    $于是$T_M$单调递增且有上界，说明收敛，令其极限为$T$.

    由于$f$是双射，其逆函数$f^(-1):NN->NN$也是一个双射，并有
    $
        a_n = a_(f(f^(-1)(n)))
    $于是可以将$sum_(m=0)^infinity a_(f(m))$看作是原级数，$sum_(n=0)^infinity a_(f(f^(-1)(n))) = sum_(n=0)^infinity a_n$是重排级数，重复上面就有
    $
        S = sum_(n=0)^infinity a_n <= sum_(m=0)^infinity = T
    $于是就有$S = T$，非负级数重排不改变值

]

#proposition[绝对收敛级数重排不改变值][
    $sum_(n=0)^infinity a_n$绝对收敛，$f:NN->NN$是双射，那么$sum_(m=0)^infinity a_(f(m))$也绝对收敛且有
    $
        sum_(n=0)^infinity a_n = sum_(m=0)^infinity a_(f(m))
    $
]<proposition:absolute-convergent-series-rearrangment>
#proof[
    由于$sum_(n=0)^infinity a_n$绝对收敛，那么令$L := sum_(n=0)^infinity abs(a_n), L in RR^+$，这是一个非负级数，那么由@propositon:non-neg-series-rearrangment 也有$L = sum_(m=0)^infinity abs(a_(f(m)))$
    由@lem:test-absolute-convergent 就有原级数和重排级数也是收敛的，令$L' = sum_(n=0)^infinity a_n$，那么需要证明$sum_(m=0)^infinity a_(f(m))$也收敛到$L'$

    由于$sum_(n=0)^infinity abs(a_n)$收敛，那么任取$epsilon/2 in RR^+$，存在$N_1 >= 0, forall p, q >= N_1, sum_(n=p)^q abs(a_n) <= epsilon/2$；由于$sum_(n=0)^infinity a_n -> L'$，那么存在$N >= N_1$，使得$abs(sum_(n=0)^N a_n - L') <= epsilon/2$

    由于$f:NN->NN$是双射，那么逆函数$f^(-1): NN->NN$也是双射，易知$(f^(-1)(n))_(n=0)^N$是有限的，那么也就有界，令上界为$M$，于是$forall M' >= M$，易有${f^(-1)(n): n <=N} subset.eq {m in NN: m <=M'}$，由于$f$是双射，那么这两个集合的前像就有如下成立
    $
        E & = f({f^(-1)(n): n<=N}) = {n in NN: n<=N} \
        F & = f({m in NN: m<=M'}) = {f(m): m <= M'} \
          & => E subset.eq F
    $于是接着有
    $
        sum_(m=0)^(M')a_(f(m)) = sum_(n in F)a_n = sum_(n=0)^N a_n + sum_(n in F without E)a_n
    $易知$F without E$也是有限的，进而存在$q in NN$，使得$F without E subset.eq{n in NN: N+1 <= n <= q}$，由于$q ,N+1 > N >=N'$于是就有
    $
        abs(sum_(n in F without E) a_n) <= sum_(n in F without E) abs(a_n) <= sum_(n = N+1)^q abs(a_n) <= epsilon/2
    $结合先前的结果，就有
    $
        sum_(m=0)^(M')a_(f(m)) &= sum_(n=0)^N a_n + sum_(x in F without E) a_n <= sum_(n=0)^N a_n + epsilon/2 \ &=> abs(sum_(m=0)^(M') a_(f(m)) - sum_(n=0)^N a_n) <= epsilon/2
    $再由
    $
        abs(sum_(n=0)^N a_n - L') <= epsilon/2
    $就有
    $
        abs(sum_(m=0)^M' a_(f(m)) - L') <= abs(sum_(m=0)^(M') a_(f(m)) - sum_(n=0)^N a_n) + abs(sum_(n=0)^N a_n - L') <= epsilon
    $于是绝对收敛级数在重排后仍然有相同的值
]

#problem[
    $sum_(n=0)^infinity a_n$绝对收敛，$f:NN->NN$是严格单调递增函数，那么$sum_(n=0)^infinity a_(f(n))$也是绝对收敛的，如果$f:NN->NN$只是一个双射，会有什么结果？
]
#proof[
    原级数是绝对收敛的，需要证明$sum_(n=0)^N abs(a_(f(n)))$也是收敛的

    任取$N in NN$，记$sum_(n=0)^infinity abs(a_(f(n)))$的前$N$项和为$T_N := sum_(n=0)^N abs(a_(f(n)))$，定义集合$E = {f(n) : n in NN, n<=N}$，由于$f:NN->NN$是严格递增的，那么该集合的最大值为$f(N)$

    对于$sum_(n=0)^infinity abs(a_n)$来说，其前$f(N)$项和为$S'_N := sum_(n=0)^(f(N)) abs(a_n)$，于是定义集合$F = {n in NN: n <= f(N)}$，易知$E subset.eq F$，那么就有
    $
        S'_N & = sum_(n=0)^(f(N)) abs(a_n)   & = sum_(n in F) abs(a_n) \
         T_N & = sum_(n=0)^(N) abs(a_(f(n))) & = sum_(n in E) abs(a_n)
    $接着有
    $
        T_N = sum_(n in E) abs(a_n) <= sum_(n in F) abs(a_n) = S'_N
    $于是$sum_(n=0)^infinity a_(f(n))$也是绝对收敛的

    如果$f:NN->NN$是双射，由@proposition:absolute-convergent-series-rearrangment 可知也是收敛的
]

#problem[使用@propositon:non-neg-series-rearrangment 和@prop:infinitie-series-law 重新证明@proposition:absolute-convergent-series-rearrangment]
#proof[
    $sum_(n=0)^infinity a_n$是绝对收敛的，那么$sum_(n=0)^infinity abs(a_n)$是非负收敛的，那么由@propositon:non-neg-series-rearrangment 可知$sum_(m=0)^infinity abs(a_(f(m)))$也是收敛的，进而$sum_(m=0)^infinity a_(f(m))$是绝对收敛的，接下来证明绝对收敛级数重排不改变值

    有恒等式
    $
        a_n = a_n + abs(a_n) - abs(a_n)
    $其中令$b_n := a_n - abs(a_n)$，$c_n := abs(a_n)$，易知$0 <= b_n <= 2abs(a_n), c_n >= 0$，于是由@propositon:non-neg-series-rearrangment，$sum_(m=0)^infinity b_(f(m))$和$sum_(m=0)^infinity c_(f(m))$都是收敛的，并且有
    $
        sum_(n=0)^infinity b_n = sum_(m=0)^infinity b_(f(m))\
        sum_(n=0)^infinity c_n = sum_(m=0)^infinity c_(f(m))\
    $由@prop:infinitie-series-law 就有
    $
        sum_(n=0)^infinity a_n & = sum_(n=0)^infinity (a_n + abs(a_n) - abs(a_n)) \
        & = sum_(n=0)^infinity b_n + sum_(n=0)^infinity c_n\
        & = sum_(m=0)^infinity b_(f(m)) + sum_(m=0)^infinity c_(f(m)) \
        & = sum_(n=0)^infinity a_(f(m))
    $得证
]

== 根值测试和比值测试

#theorem[根值测试][
    $sum_(n=m)^infinity a_n$是一个实无穷级数，令$alpha := limsup_(n->infinity) abs(a_n)^(1/n)$
    + $alpha < 1 => sum_(n=0)^infinity a_n$绝对收敛
    + $alpha > 1 => sum_(n=0)^infinity a_n$不收敛
    + $alpha = 1$，无法得到任何结论
]<thm:root-test>
#proof[
    不失一般性，考虑$m>=1, n>=m$
    1. 当$alpha < 1$时，由于$forall n>=m, abs(a_n)^(1/n) > 0$，那么自然有$0 < alpha < 1$，于是存在$epsilon in RR^+$，满足
        $ 0 < alpha < alpha + epsilon < 1 $
        由于$alpha$是$(abs(a_n)^(1/n))_(n=m)^infinity$的上极限，那么就有
        $
            exists N >=m, forall n>=N, abs(a_n)^(1/n) < alpha + epsilon => abs(a_n) < (alpha + epsilon)^n
        $由@lem:geometry-series 就有几何级数$sum_(n=N)^infinity (alpha+epsilon)^n$收敛，再由@coro:comparison-test 可知$sum_(n=N)^infinity abs(a_n)$收敛，那么根据
        $
            sum_(n=m)^infinity abs(a_n) = sum_(n=m)^(N-1) abs(a_n) + sum_(n=N)^infinity abs(a_n)
        $和@prop:infinitie-series-law 可知$sum_(n=m)^infinity abs(a_n)$收敛，所以$sum_(n=0)^infinity a_n$绝对收敛
    2. 当$alpha > 1$时，有
        $
            forall N >=m, exists n >=N, abs(a_n)^(1/n) > 1 => abs(a_n) > 1
        $说明$(a_n)_(n=m)^infinity$无法收敛到$0$，因此由@coro:zero-test-infinite-series 可知$sum_(n=0)^infinity a_n$不收敛

    3. 当$alpha = 1$时无法判断收敛性，使用特例进行证明，对于级数$sum_(n=1)^infinity 1/n$和级数$sum_(n=1)1/n^2$，二者上极限都是$1$，然前者发散、后者收敛
]

#note-block[
    在根值测试中使用了上极限的说法，如果知道序列$(abs(a_n)^(1/n))_(n=m)^infinity$是收敛的话，用极限而非上极限也是可以的，因为序列收敛时上极限等于极限
]

#lemma[$(c_n)_(n=m)^infinity$是正实数序列，有以下成立
    $
        liminf_(n->infinity) c_(n+1)/c_n <= liminf_(n->infinity) c_n^(1/n) <= limsup_(n->infinity) c_n^(1/n) <= limsup_(n->infinity) c_(n+1)/c_n
    $
]<lem:lem-for-contrast-test>
#proof[

    1. 中间的不等式由@prop:sequence-limit-point-properties 易得

    2. 对于右边的不等式，令$L := limsup_(n->infinity) c_(n+1)/c_n$，当$L = +infinity$时显然成立，同时由于$(c_n)_(n=m)^infinity$是正实数序列，那么$L != -infinity and L in RR_(>= 0)$，取$epsilon in RR^+$，就有$L+epsilon > L$，于是由@prop:sequence-limit-point-properties 就有
        $
            exists N >= m, forall n>=N, c_(n+1)/c_n <= L + epsilon
        $不失一般性，令$N >= 1$，于是就有
        $
            c_(n+1) <= c_n (L + epsilon)
        $假设满足$forall n>= N, c_n <= c_N (L+epsilon)^(n-N)$，对$n - N$归纳，当$n-N=0$时，有$c_n <= c_n$，显然对任意$n>=N$成立，现在归纳性的假设$n-N = m$时成立，证明$n-N=m+1$的情况，由已知$c_(n+1) <= c_n (L +epsilon)$就有
        $
            c_n = c_(N+m+1) <= c_(N+m) (L+epsilon)
        $由归纳假设就有
        $
            & c_(n) <= c_N (L+epsilon)^(n-N) \
            & => c_(N+m) <= c_N (L+epsilon)^m \
            & => c_(N+m+1) <= c_(N+m) (L + epsilon) <= c_N (L+epsilon)^(m+1) \
            & => c_n <= c_N (L + epsilon)^(n - N)
        $归纳结束

        令$A := c_N (L + epsilon)^(-N) in RR^+$，就有
        $
            c_n <= A (L+epsilon)^n => c_n^(1/n) <= A^(1/n) (L+epsilon), forall n >= N
        $于是有
        $
            lim_(n->infinity) A^(1/n) (L+epsilon) = L+epsilon
        $于是由@lem:comparison-lemma 就有
        $
            limsup_(n->infinity) c_n^(1/n) <= L + epsilon
        $由于是对任意$epsilon in RR^+$成立的，于是
        $
            limsup_(n->infinity) c_n^(1/n) <= L = limsup c_(n+1)/c_n
        $

    3. 对于左边的不等式，令$L = liminf_(n->infinity) c_(n+1)/c_n$，易知$L$不可能为正负无穷，且由于是正实数序列，那么$L in RR_(>= 0)$，任取$epsilon in RR^+$，就有
        $
            L - epsilon < L
        $于是根据@prop:sequence-limit-point-properties 就有
        $
            exists N >=m, forall n >= N, L -epsilon <= c_(n+1)/c_n
        $假设有$c_n >= c_N (L - epsilon)^(n-N), forall n >=N$成立，使用如2中的归纳法可以证明，接着令$A := c_N (L - epsilon)^(-N)$，就有
        $
            c_n >= (L - epsilon)^n A => c_n^(1/n) >= (L -epsilon) A^(1/n)
        $对于后者有
        $
            lim_(n->infinity) (L -epsilon) A^(1/n) = L - epsilon
        $由@lem:comparison-lemma 就有
        $
            liminf_(n->infinity) c_n^(1/n) >= L - epsilon
        $由于$epsilon$是任取的，就有
        $
            liminf_(n->infinity) c_n^(1/n) >= L = liminf_(n->infinity) c_(n+1)/c_n
        $

]

#corollary[比值测试][
    $sum_(n=m)^infinity a_n$是非零实数无穷序列，那么有
    + 如果$limsup_(n->infinity) abs(a_(n+1))/abs(a_n) < 1$，那么$sum_(n=m)^infinity a_n$绝对收敛
    + 如果$liminf_(n->infinity) abs(a_(n+1))/abs(a_n) > 1$，那么$sum_(n=m)^infinity a_n$不收敛
    + 其他情况下，得不到任何结论
]
#proof[
    1. 由@lem:lem-for-contrast-test 可知
        $
            limsup_(n->infinity) abs(a_n)^(1/n) <= limsup_(n->infinity) abs(a_(n+1))/abs(a_n) < 1
        $再由@thm:root-test 可知$sum_(n=m)^infinity a_n$绝对收敛

    2. 由@lem:lem-for-contrast-test 可知
        $
            1 < liminf_(n->infinity)abs(a_(n+1))/abs(a_n) <= limsup_(n->infinity) abs(a_n)^(1/n)
        $再由@thm:root-test 可知$sum_(n=m)^infinity a_n$发散

    3. 无法判定$limsup_(n->infinity) abs(a_n)^(1/n)$与$1$的关系

]

#proposition[
    $lim_(n->infinity)n^(1/n) = 1$
]
#proof[
    由@lem:lem-for-contrast-test 就有
    $
        & limsup_(n->infinity) n^(1/n) <= limsup_(n->infinity) (n+1)/n = 1 \
        & liminf_(n->infinity) n^(1/n) >= liminf_(n->infinity) (n+1)/n = 1
    $再由@prop:sequence-limit-point-properties 可知
    $
        lim_(n->infinity)n^(1/n) = 1
    $
]

#problem[证明@lem:lem-for-contrast-test][见前]
#problem[$x,q in RR and abs(x) < 1$，证明级数$sum_(n=1)^infinity n^q x^n$绝对收敛，且有$lim_(n->infinity)n^q x^n = 0$]
#proof[
    易有
    $
        lim_(n->infinity) abs(n^q x^n)^(1/n) = lim_(n->infinity) (n^(1/n))""^q abs(x) = 1^q abs(x) = abs(x) < 1
    $@thm:root-test 可知$sum_(n=1)^infinity n^q x^n$绝对收敛，进而是收敛的，所以根据@coro:zero-test-infinite-series 可知
    $
        lim_(n->infinity)n^q x^n = 0
    $
]

#problem[
    试举一例：$sum_(n=1)^infinity a_n$是一个正实数级数，满足$lim_(n->infinity)a_(n+1)/a_n = lim_(n->infinity)a_n^(1/n) = 1$，但是级数却是发散的;

    试举一例：$sum_(n=1)^infinity b_n$是一个正实数级数，满足$lim_(n->infinity)b_(n+1)/b_n = lim_(n->infinity)b_n^(1/n) = 1$，级数是收敛的;

]
#solution[
    1. $a_n = 1/n$，满足$lim_(n->infinity) n/(n+1) = 1$，且$lim_(n->infinity)(1/n)^(1/n) = lim_(n->infinity) (n^(1/n))""^(-1) = 1$，但是$sum_(n=1)^infinity 1/n$是发散的
    2. $b_n = 1/n^2$，满足$lim_(n->infinity)n^2/(n+2)^2 = 1$，且$lim_(n->infinity)(1/n^2)""^(1/n) = lim_(n->infinity)(n^(1/n))^(-2) = 1$，但是$sum_(n=1)^infinity 1/n^2$是收敛的
]
#pagebreak()
