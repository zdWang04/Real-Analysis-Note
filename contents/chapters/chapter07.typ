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

#lemma[有限级数的性质][
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
]<lem:finite-series-algebra>

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
]
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

#problem[证明@lem:finite-series-algebra]
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


#pagebreak()
