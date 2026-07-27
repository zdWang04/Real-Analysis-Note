#import "@preview/euler-math:0.1.0": *
#import "@preview/theorion:0.6.0": proposition
#import "../utils/utils.typ" : *

= 集合论

== 基础知识

== 罗素悖论

== 函数

== 像与逆像

== 笛卡尔积

#definition(title: "有序对")[如果 $x$ 和 $y$ 是两个对象，那么他们的_有序对 $(x,y)$ _也是一个对象，其中 $x$ 是有序对的第一个组分， $y$ 是有序对的第二个组分。
  $ (x, y) = (x', y') <==> x = x' and y = y' $
]

#definition(title: "笛卡尔积")[
  如果 $X$ 和 $Y$ 都是集合，那么定义_笛卡尔积_为 $X times Y$ 是一个有序对的集合，这些有序对的第一个元素是 $X$ 中的元素，第二个则是 $Y$ 中的元素
  $ X times Y = {(x, y): x in X, y in Y} $
]

#note-block[可以将加法构造为一个函数 $+:N times N -> N$ ，该函数被定义为 $(x, y) |-> x+y$ ]

#definition(title: [有序$n$-元组和$n$-次笛卡尔积])[
  $n$为一个自然数，一个有序$n$元对$(x_i)_(1 <= i <= n)$（也可写作$(x_1, x_2, ..., x_n)$）是对象$x_i$的组合，其中$x_i$是有序$n$-元组的第$i$个组分。两个有序$n$-元组是相等的，当且仅当对应组分相等。
  $ (x_i)_(1 <= i <= n) = (y_i)_(1 <= i <= n) <==> x_i = y_i, forall 1<= i <= n $ 

  如果$(X_i)_(1<=i<=n)$是一个集合的有序$n$-元组，那么可以定义它的_笛卡尔积$product_(1<=i<=n)X_i$_为
  $ product_(1<=i<=n)X_i := {(x_i)_(1<=i<=n): x_i in X_i, forall 1 <= i <=n} $
]

#note-block[
  有序$n$-元组也被称为_$n$个元素的有序序列_，或称_有限序列_
]
#pagebreak()
#note-block[
  如果$x$是一个对象，那么_1-元组$(x)$_被认为和$x$是相等的，尽管严格来说是不一样，但是并不影响。
]

#note-block[
  如果$X_1$是一个集合，那么$product_(1<=i<=1)X_i = X_1$
  
  #proof[
    + $i$ 唯一的取值是1，由定义1.3， $ product_(1<=i<=1)X_i={x_1 : x_1 in X_1} subset.eq X_1 $
    + 另外一方面，$forall x in X_1$，都有$x in {x_1 : x_1 in X_1} = product_(1<=i<=1)X_i$，那么$X_1 subset.eq product_(1<=i<=1)X_i$ \ \
    + 综上 $product_(1<=i<=1)X_i = X_1$
  ]
]

#note-block[
   + 空笛卡尔积$product_(1<=i<=0)X_i$的计算结果是 ${()}$ 
   + ${()}$ 不是空集
   + ${()}$ 唯一的元素是_0-元组（或称空元组） $()$_
]

#note-block[
  如果$n$是一个自然数，记$X^n := product_(1<=i<=n)X$ 为$X$的$n$-次笛卡尔积，在忽略$x$和$(x)$区别的前提下$X^1 = X$，$X^0={()}$

  #proof[
    - $X^1 = X$ 实际上就是 $product_(1<=i<=1)X_i = X_1$，这在前面的侧记中已经证明

    - $X^0 = {()}$ \ \
      + 由定义1.3，$X^0 = product_(1<=i<=0)X$ \ \
      + 由于$product_(1<=i<=0)X_i = {()}$ \ \
      + $X_i$的选取并不影响上面的结果
      + 所以$X^0 = {()}$
  ]
]

#lemma(title: "有限选取")[
  令$n >= 1$是一个自然数，并且对于任何自然数$1<= i <= n$，$X_i$都是非空集合，那么存在一个$n$-元组$(x_i)_(1<=i<=n)$，对于任意的$1<=i <= n$，都使得$x_i in X_i$成立，也即若任一个$X_i$非空，那么$product_(1<=i<=n)X_i$也非空。
  #proof[
  对$n$进行归纳。
  + $n=0$时，$i$取值为空，空真自动成立
  + $n=1$时，命题变为对于非空集合$X_1$，存在一个一元组$(x_1)$（或称对象$x_1$）$x_1 in X_1$，根据单个选取引理，如果集合非空，那么必然存在某个元素属于该集合，所以成立。
  + 现在归纳的假设在$n$的情况下成立。
  + 由于归纳假设，存在$(x_i)_(1<=i<=n)$，对于$forall 1<= i <= n$ 使得 $x_i in X_i$ 成立。在$n++$的情况下，由于$X_(n++)$非空，再次根据单个选取引理，一定存在对象 $a in X_(n++)$ ，现在令新的(n++)-元组为$(y_i)_(1<=i <= n++)$，其中$y_i = x_i, forall 1<= i <= n$ 且 $y_(i) = a, i = n++$ ，这样的(n++)-元组是存在的，所以$y_i in X_i, forall 1<= i <= n++$
  + 综上归纳完毕
]
]



#problem[
  1. 证明有序对$(x, y) = {{x}, {x, y}}$满足$(x, y) = (x', y') <==> x = x' and y = y'$
  #proof[
    - $(x, y) = (x', y') ==> x = x' and y = y'$

      1. 当$x = y$时，$(x, y) = {{x}}$，那么如果$(x, y) = (x', y')$，便有${{x}} = {{x'}}$，对于这个单元素集合，也就是${x} = {x'}$，再次利用单元素集合，就有$x = x' = y = y'$ 
      2. 当$x != y$时，$(x, y) = {{x}, {x, y}}$，那么如果$(x, y) = (x', y')$，便有${{x}, {x, y}} = {{x'}, {x', y'}}$，等式两边的集合都是双元素集合，且一个是单元素集合，另一个是双元素集合，只能令其对应相等，也即$ {x} = {x'}\ {x, y} = {x', y'} $所以有$x = x'$，又因为$x != y$，所以$x' != y$，只能是$y = y'$
      3. 考虑了所有的情况，得证

    - $x = x' and y = y' ==> (x, y) = (x', y')$
      
      若$x = x' and y = y'$，代入定义x就可以得到$(x, y) = (x', y')$
  ]
  2. $X$和$Y$是集合，证明$X times Y$也是一个集合
  #proof[
    + $forall x in X, forall y in Y"有" x in X union Y, y in X union Y$，令任意集合$X$的幂集为$cal(P)(X)$

    那么，${x}, {x, y} in cal(P)(X union Y)$，于是${{x}, {x, y}} subset.eq cal(P)(X union Y)$，所以就有
    $ (x, y) = {{x}, {x, y}} subset.eq cal(P)(cal(P)(X union Y)) $
    至此，证明了对于集合$X"和"Y$，$X times Y$中的元素（也即有序对$(x, y)$们）都生活在 $cal(P)(cal(P)(X union Y))$ 中
    2. 现在定义笛卡尔积为$ X times Y := {z in cal(P)(cal(P)(X union Y)):exists x in X, exists y in Y, z = {{x}, {x, y}}} $
    幂集公理保证$cal(P)(cal(P)(X union Y))$一定是集合，且分类条件明确，那么根据分类公理，$X times Y$也是一个集合

  ]
]

#problem[
定义一个有序$n$-元组是一个满射函数$x: {i in NN: 1<= i <= n} -> X$，其值域为任意集合$X$，将$x_i$写作$x(i)$，将$x$写作$(x_i)_(1 <= i <= n)$，验证$ (x_i)_(1 <= i <= n) = (y_i)_(1<=i<=n) <==> forall 1<= i <= n, x_i = y_i $
    #proof[
      + $(x_i)_(1 <= i <= n) = (y_i)_(1<=i<=n) ==> forall 1<= i <= n, x_i = y_i$
        
        函数$x$与函数$y$相等，那么$forall 1<= i <= n, x(i) = y(i)$，也即$forall 1<= i <= n, x_i = y_i$
      + $forall 1<= i <= n, x_i = y_i ==> (x_i)_(1 <= i <= n) = (y_i)_(1<=i<=n)$
        
        $forall 1<= i <= n, x_i = y_i$说明在定义域上两个函数逐点相等，那么函数$x$和函数$y$相等，那么根据定义$x = y ==> (x_i)_(1<=i<=n) = (y_i)_(1<=i<=n)$
    ]
]

#problem[
   证明有序对和$n$-元组的相等是满足自反、对称和传递性的

   #proof[
    1. 自反 $(x_i)_(1<=i<=n) = (x_i)_(1<=i<=n)$
      
      由于$x = x$对于集合和元素成立，那么$forall 1 <= i <= n, x_i = x_i$成立，根据定义，$(x_i)_(1<=i<=n) = (x_i)_(1<=i<=n)$成立
    
    2. 对称 $(x_i)_(1<=i<=n) = (y_i)_(1<=i<=n) <==> (y_i)_(1<=i<=n) = (x_i)_(1<=i<=n)$
      
      对于任意元素和集合，$x = y <==> y = x$，那么根据定义展开有$forall 1 <= i <= n, x_i = y_i, y_i = x_i$，反向同理，所以对称性得证
    3. 传递 $(x_i)_(1<=i<=n) = (y_i)_(1<=i<=n) and (y_i)_(1<=i<=n) = (z_i)_(1<=i<=n) ==> (x_i)_(1<=i<=n) = (z_i)_(1<=i<=n)$
      
      对于任意元素和集合，$x = y and y = z ==> x = z$成立，于是$forall 1<=i<=n, x_i = y_i, y_i = z_i ==> x_i = z_i$，根据定义传递性得证

    上述的证明在$n = 2$时也成立，于是有序对的相等也满足自反、对称和传递性
   ]
   
]

#problem[
  $A,B,C$是集合，证明$A times (B union C) = (A times B) union (A times C)$，$A times (B inter C) = (A times B) inter (A times C)$，$A times (B without C) = (A times B) without (A times C)$
  #proof[
    
    - $A times (B union C) = (A times B) union (A times C)$
      
      + $ &forall (x,y) in A times (B union C) \  &=> x in A and y in B union C \ &=> x in A and (y in B or y in C) \ &=> (x in A and y in B) or (x in A and y in C) \ &=> (x,y) in A times B or (x, y) in A times C \ &=>(x,y) in (A times B) union (A times C) \ &=> A times (B union C) subset.eq (A times B) union (A times C) $
      
      + $ &forall (x, y) in (A times B) union (A times C) \ &=> (x, y) in A times B or (x, y) in A times C \ &=> (x in A and y in B) or (x in A and y in C) \ &=> x in A and (y in B or y in C) \ &=> (x, y) in A times (B union C) \ &=> (A times B) union (A times C) subset.eq A times (B union C) $
      
      + 综上$A times (B union C) = (A times B) union (A times C)$
    
    - $A times (B inter C) = (A times B) inter (A times C)$
      
      + $ &forall (x, y) in A times (B inter C) \ &=> x in A and y in B inter C \ &=> x in A and (y in B and y in C) \ &=> (x in A and y in B) and (x in A and y in C) \ &=> (x, y) in (A times B) inter (A times C) \ &=> A times (B inter C) subset.eq (A times B) inter (A times C) $
      
      + $ &(x, y) in (A times B) inter (A times C) \ &=> (x, y) in (A times B) and (x, y) in A times C \ &=> (x in A and y in B) and (x in A and y in C) \ &=> x in A and (y in B and y in C) \ &=> x in A and y in (B inter C) \ &=> (x, y) in A times (B inter C) \ &=> (A times B) inter (A times C) subset.eq A times (B inter C) $ 
      
      +  综上$A times (B inter C) = (A times B) inter (A times C)$
    
    - $A times (B without C) = (A times B) without (A times C)$
      
      + $ &forall (x, y) in A times (B without C) \ &=> x in A and y in B without C \ &=> x in A and (y in B and y in.not C) \ &=> (x in A and y in B) and (x in A and y in.not C) $ 由于$x in A and y in B$，那么$x in A times B$，如果$(x, y) in A times C$，那么$x in A and y in C$，这与$y in.not C$矛盾，所以$(x, y) in.not A times C$，所以$ &(x in A and y in B) and (x in A and y in.not C)  \ &=> (x, y) in (A times B) without (A times C)\  &=> A times (B without C) subset.eq (A times B) without (A times C) $
      
      2. $ &forall (x, y) in (A times B) without (A times C) \ &=> (x,y) in A times B and (x, y) in.not A times C \ &=> x in A and y in B and y in.not C \ &=> x in A and y in (B without C) \ &=> (x, y) in A times (B without C) \ &=> (A times B) without (A times C) subset.eq A times (B without C) $
      
      3. 综上$(A times B) without (A times C) = A times (B without C)$
  ]
]

#problem[
  $A,B,C,D$是集合，证明$(A times B) inter (C times D) = (A inter C) times (B inter D)$。$(A times B) union (C times D) = (A union C) times (B union D)$ 是否为真？$(A times B) without (C times D) = (A without C) times (B without D)$是否为真？
  #proof[
    
    - $(A times B) inter (C times D) = (A inter C) times (B inter D)$
      
      + $ &forall (x, y) in (A times B) inter (C times D) \ &=> (x, y) in (A times B) and (x, y) in (C times D) \ &=> x in A and y in B and x in C and y in D \ &=> x in A and x in C and y in B and y in D \ &=> x in (A inter C) and y in (B and D) \ &=> (x, y) in (A inter C) times (B inter D) \ &=> (A times B) inter (C times D) subset.eq (A times C) inter (B times D) $
      
      + $ &forall (x, y) in (A inter C) times (B inter D) \ &=> x in A inter C and y in B inter D \ &=> x in A and x in C and y in B and y in D \ &=> (x in A and y in B) and (x in C and y in D) \ &=> (x,y) in (A times B) and (x, y) in (C times D) \ &=> (x, y) in (A times B) inter (C times D) \ &=> (A inter C) times (B inter D) subset.eq (A times B) inter (C times D) $
      
      + 综上$(A times B) inter (C times D) = (A inter C) times (B inter D)$
    
    - $(A times B) union (C times D) = (A union C) times (B union D)$ 是否为真？
      
      + $ &forall (x, y) in (A times B) union (C times D) \ &=> (x,y) in (A times B) or (x, y) in (C times D) \ &=> (x in A and y in B) or (x in C and y in D) \ &=> x in (A union C) and y in (B union D) \ &=> (x,y) in (A union C) times (B union D) \ &=> (A times B) union (C times D) subset.eq (A union C) times (B union D) $ 
      
      + $ &forall (x, y) in (A union C) times (B union D) \ &=> x in (A union C) and y in (B union D) \ &=> (x in A or x in C) and (y in B or y in D) \ &=> (x in A and y in B) or (x in A and y in D) or (x in C and y in B) or (x in C and y in D) \ &=> (x, y) in (A times B) union (A times D) union (C times B) union (C times D)\ &!= (A times B) union (C times D) $
      
      + 综上，二者并不相等，而是$(A times B) union (C times D) subset.neq (A union C) times (B union D)$
    
    - $(A times B) without (C times D) = (A without C) times (B without D)$是否为真？
      
      + $ &forall (x, y) in (A times B) without (C times D) \ &=> (x, y) in (A times B) and (x, y) in.not (C times D) \ &=> (x in A and y in B) and (x in.not C or y in.not D) \ &=> (x in A and y in B and x in.not C) or (x in A and y in B and y in.not D) \ &=> (x in A and x in.not C and y in B) or (x in A and y in B and y in.not D) \ &=> (x in A without C and y in B) or (x in A and y in B without D) \ &=> (x,y) in (A without C)times B or (x, y) in A times (B without D) $ 注意，$(A without C times B) union (A times B without D)$实际上是$(A times B) without (C times D)$的正确展开形式，且不等于$(A without C) times (B times D)$
      
      + $ &forall (x, y) in (A without C) times (B without D) \ &=>x in A without C and y in B without D\ & => x in A and x in.not C and y in B and y in.not D \ &=> x in A and y in B and x in.not C and y in.not D \ &=>(x, y) in A times B and (x, y) in.not C times D\ &=>(x, y)  in (A times B) without (C times D) $ 注意，$(x ,y) in.not C times D <=> x in.not C or y in.not D$，所以$x in.not C and y in.not D$是$(x, y) in.not C times D$的充分但非必要条件。

      + 综上，$(A without C) times (B without D) subset.neq (A times B) without (C times D)$
  ]
]

#problem[
  $A,B,C,D$是非空集合，$A times B subset.eq C times D <=> A subset.eq C and B subset.eq D$，$A times B = C times D <=> A = C and B = D$，若移除$A,B,C,D$是非空的这个条件，会发生什么？

  #proof[
    - $A times B subset.eq C times D <=> A subset.eq C and B subset.eq D$
      + $A times B subset.eq C times D => A subset.eq C and B subset.eq D $

        $ &A times B subset.eq C times D\ &=>forall (x, y) in A times B, (x, y) in C times D\ &=>x in A and y in B, x in C and y in D \ &=> A subset.eq C and B subset.eq D $
      + $A subset.eq C and B subset.eq D => A times B subset.eq C times D$

        $ &forall (x, y) in A times B\ &=>x in A and y in B $由已知，$forall x in A, x in C and forall y in B, y in D$，所以接着有 $ &=> x in C and y in D \ &=> (x, y) in C times D \ &=> A times B subset.eq C times D $
    
      + 综上，$A times B subset.eq C times D <=> A subset.eq C and B subset.eq D$在$A, B,C,D != emptyset$时成立
      
      + 特别的，比如$A = C = emptyset and B subset.eq.not D$，$A times B = emptyset subset.eq C times D = emptyset$成立，但是$B subset.eq D$为假，因为$B subset.eq.not D$ 
    
    - $A times B = C times D <=> A = C and B = D$
      + $A times B =C times D => A = C and B = D$
        
        $ &forall (x, y) in A times B \ &=> x in A and y in B $由于$A times B = C times D$，那么接着可以得到$ &x in C and y in D \ &=> A subset.eq C and B subset.eq D $同理对$forall (x, y) in C times D$进行推理，可得$C subset.eq A and D subset.eq B$，所以可得$A = C and B = D$
      
      + $A = C and B = D => A times B = C times D$

        $ &forall (x, y) in A times B \ &=> x in A and y in B $由于$A = C and B = D$，所以接着有$ &=>x in C and y in D \ &=>(x, y) in C times D \ &=> A times B subset.eq C times D $同理对$forall (x, y) in C times D$进行推理，可得$C times D subset.eq A times B$，所以可得$A times B = C times D$
      
      + 综上，$A = C and B = D <=> A times B = C times D$在$A, B,C,D != emptyset$时成立

      + 特别的，当$A = C = emptyset and B != D$时，$A times B = C times D = emptyset$，但是$A = C and B = D$为假，因为$B != D$
  ]

]

#problem[
  $X,Y$是集合，函数$pi_(X times Y -> X):X times Y -> X$被定义为$pi_(X times Y -> X)(x,y) = x$；函数$pi_(X times Y -> Y):X times Y -> Y$被定义为$pi_(X times Y -> Y)(x,y) = y$，这两个函数被称为定义在$X times Y$上的_坐标函数（co-ordinate functions）_，证明对于任意函数$f:Z -> X$和$g:Z -> Y$，存在唯一一个函数$h: Z -> X times Y$使得$pi_(X times Y -> X) compose h = f$和$pi_(X times Y -> Y) compose h = g$成立

  #proof[
    
    - 存在性
    
      令函数$h:Z -> X times Y, forall z in Z, z |-> (f(z), g(z))$，这个函数满足定义，是存在的
    
      $ &(pi_(X times Y -> X) compose h)(z)\ &= pi_(X times Y -> X)(h(z))\ &= pi_(X times Y -> X)(f(z), g(z)) = f(z) $
  
      $ &(pi_(X times Y -> Y) compose h)(z)\ &= pi_(X times Y -> Y)(h(z))\ &= pi_(X times Y -> Y)(f(z), g(z)) = g(z) $

      所以$pi_(X times Y -> X) compose h = f and pi_(X times Y -> Y) compose h = g$成立

    - 唯一性

      假设有$h_1, h_2$满足条件

      $ pi_(X times Y -> X) compose h_1 = &f = pi_(X times Y -> X) compose h_2 \ pi_(X times Y -> Y) compose h_1 = &g = pi_(X times Y -> Y) compose h_2 $

      $ &forall z in Z , h_1(z) = (f(z), g(z))\  h_1(z) &= (pi_(X times Y -> X)(h_1(z)), (pi_(X times Y -> Y)(h_1(z))))\ &= (pi_(X times Y -> X)(h_2(z)), (pi_(X times Y -> Y)(h_2(z)))) \ &=h_2(z) $

      所以$h_1 = h_2$，综上这样的$h$是存在且唯一的
  ]
]

#note-block[这样的函数$h$被称为$f"和"g$的_直和（direct sum）_，并记作_$h = f plus.o g$_]

#problem[
  $X_1, ..., X_n$是集合，证明$product_(i=1)^n X_i = emptyset <==> exists 1<=i<=n,X_i = emptyset$

  #proof[
    - $product_(i=1)^n X_i = emptyset => exists 1<= i<= n, X_i = emptyset$
    
      $ product_(i=1)^n X_i=emptyset$，即存在一个$i$使得$x_i in X_i, forall 1<=i<=n$不成立，由于空集中没有任何元素，所以$exists 1<=i<=n, X_i = emptyset$

    - $exists 1<= i<= n, X_i = emptyset => product_(i=1)^n X_i = emptyset$
    
      由于$exists 1<=i<=n, X_i = emptyset$，不妨令$X_j = emptyset, 1<=j<=n$，那么$x_j in.not X_j$，于是$product_(i=1)^(n)X_i = emptyset$

    - 综上，$product_(i=1)^n X_i = emptyset <==> exists 1<=i<=n,X_i = emptyset$]
]

#problem[
  $I,J$是集合，$forall alpha in I, A_alpha$是集合，$forall beta in J, B_beta$是集合，证明$(union.big_(alpha in I) A_alpha) inter (union.big_(beta in J)B_beta) = union.big_((alpha, beta) in I times J)(A_alpha inter B_beta)$

  #proof[
    
    + $ &forall x in (union.big_(alpha in I)A_alpha) inter (union.big_(beta in J)B_beta)\ &=>x in union.big_(alpha in I)A_alpha and x in union.big_(beta in J)B_beta\ &=> exists alpha in I, x in A_alpha and exists beta in J, x in B_beta \ &=> exists (alpha, beta) in I times J, x in A_alpha and x in B_beta \ &=> x in union.big_((alpha, beta) in I times J)(A_alpha inter B_beta)\ &=> (union.big_(alpha in I)A_alpha) inter (union.big_(beta in J)B_beta) subset.eq union.big_((alpha, beta) in I times J)(A_alpha inter B_beta) $

    + $ &forall x in union.big_((alpha, beta) in I times J)(A_alpha inter B_beta)\ &=>exists (alpha, beta) in I times J, x in A_alpha and x in B_beta\ &=>exists alpha in I, exists beta in J, x in A_alpha and x in B_beta\ &=>exists alpha in I, x in A_alpha and exists beta in J, x in B_beta\ &=> x in (union.big_(alpha in I) A_alpha) inter (union.big_(beta in J) B_beta)\ &=> union.big_((alpha, beta) in I times J)(A_alpha inter B_beta) subset.eq (union.big_(alpha in I)A_alpha) inter (union.big_(beta in J)B_beta) $

    + 综上$union.big_((alpha, beta) in I times J)(A_alpha inter B_beta) = (union.big_(alpha in I)A_alpha) inter (union.big_(beta in J)B_beta)$
  ]
  
]

#problem[
  $f:X->Y$是函数，定义函数$f$的_图（graph）_为$X times Y$子集，定义为${(x, f(x)):x in X}$，证明：对于$tilde(f):X -> Y"和"f:X->Y,f=tilde(f) <==> f, tilde(f)$有相同的图。如果集合$G subset.eq X times Y$，且$forall x in X$，集合${y in Y: (x, y) in G}$中只有一个元素，证明只有一个函数$f:X->Y$的图是$G$

  #proof[
    - $f=tilde(f) <=> f, tilde(f)$有相同的图
      
      + $f=tilde(f) => f, tilde(f)$有相同的图
        
        由于$f = tilde(f)$，那么$forall x in X, f(x) = tilde(f)(x)$，于是$ {(x, f(x)):forall x in X} = {(x, tilde(f)(x)): forall x in X} $所以 $f"和"tilde(f)$有相同的图。
      
      + $f, tilde(f)$有相同的图$ => f=tilde(f)$

        由于$f, tilde(f)$有相同的图，那么$ &{(x, f(x)):forall x in X} = {(x, tilde(f)(x)): forall x in X} \ &=> forall x in X, f(x) = tilde(f)(x) $而且$f$和$tilde(f)$有相同的定义域$X$和相同的值域$Y$，所以$f = tilde(f)$
      
      + 综上，$f=tilde(f) <=> f, tilde(f)$有相同的图

    - 如果集合$G subset.eq X times Y$，且$forall x in X$，集合${y in Y: (x, y) in G}$中只有一个元素，证明只有一个函数$f:X->Y$的图是$G$

      - 存在性
        
        令函数$f:X->Y$满足$forall x in X$，$f(x)$为集合${y in Y: (x, y) in G}$中唯一的元素，也即$f(x) = y$，这是满足函数的定义的.
      
      - 唯一性
        + 假设有两个函数$f:X->Y$和$tilde(f):X->Y$满足上述条件且图均为$G$，那么$ G_f &= {(x, f(x)):forall x in X} = G \ G_(tilde(f)) &= {(x, tilde(f)(x)):forall x in X} = G \ &=> {(x, f(x)):forall x in X} = {(x, tilde(f)(x)): forall x in X}\ &=>f = tilde(f) $

        + 于是这样的函数只有一个.
  ]
]

#problem[
  证明函数空间公理可以由幂集公理推出
 
  #proof[
    令$X,Y$是任意集合，令 $cal(P)(X times Y)$是$X times Y$的幂集，根据幂集公理，它也是一个集合

    用分类公理定义$ cal(G) = {G in cal(P)(X times Y): forall x in X, exists! y in Y (x, y) in G} $

    先前证明了函数和函数的图一一对应，将$cal(G)$中的元素替换为对应的函数$ forall G in cal(G),f_G:X->Y $得到的集合正是$Y^X$
  ]
]

#problem(title: "严格的递归定义")[
  函数$f:NN times NN -> NN$，$c in NN$，证明存在一个函数$a: NN -> NN$，使得$ &a(0) = c  \  &a(n++) = f(n, a(n))，forall n in NN $成立，并且该函数是唯一的。进一步的，仅使用皮亚诺公理和集合论证明递归的定义

  #proof[
    - 存在性
      定义一个函数$a_n:{0,...,n} -> NN$，满足$ a_n (0) &= c\ a_n (k++) &= f(k, a_n (k)), forall 0<= k< n $根据替换公理，可以得到集合$cal(A) = {a_(n) : n in NN}$

      所以可以得到函数$ a = union.big cal(A) $
    
      $a:NN->NN$存在且满足要求。

    - 唯一性
      
      假设$a:NN->NN,a':NN->NN$都满足上述条件。
      $a(0) = a'(0) = c$成立，归纳性的假设$a(n) = a'(n)$也成立，现在证明$n++$下的情况
      $ a(n++) &= f(n, a(n))\ a'(n++) &= f(n, a'(n)) $由于归纳假设$a(n) = a'(n)$，那么$a(n++) = a'(n++)$，归纳完毕，$forall n in NN, a(n) = a'(n)$，且它们的定义域和值域都是$NN$，所以$a = a'$，于是这样的函数$a$是唯一的

  ]

]

#problem(title: "自然数系是唯一的")[
  假设有另一个“另类的”自然数系$NN'$，满足皮亚诺公理，证明存在一个双射$f: NN -> NN'$，满足$f(0) = 0' in NN'$，且$forall n in NN, forall n' in NN'$，有$f(n) = n' <==> f(n++) = n'++'$

  #proof[
    - 定义函数$F:NN times NN' -> NN'$，满足$ F(n, n') = n++' $由递归定义的证明，存在一个唯一函数$f:NN->NN'$满足$ f(0) &= 0' \ f(n++) &= F(n, f(n)) = n++' $

    - 单射$f(m) = f(n) => m = n$
      
      固定$n$，对$m$进行归纳，当$m = 0$时，$f(0) = 0' = f(n)$，由于$f$满足$f(0) = 0'$于是，所以$n = 0$，于是可以得到$m = n$

      现在归纳的假设$f(m) = f(n) => m = n$成立，现在证明$m++$下的情况$ f(m++) = m++' = f(n) $如果$n = 0$，就有$f(0) = 0' = m++'$，$0'$不是任何数的后继，矛盾，所以$n != 0$
      
      假设$exists k in NN, n = k++$，那么$f(m++) = m++' = f(k++) = k++'$，由于$NN'$中的后继函数$++'$是单射，所以$ m++' = k++' => m = k $由于$m,k in NN$$ m++ = k++ = n $归纳完毕
    
    - 满射$forall n' in NN', exists n in NN, f(n) = n'$
      
      对$n'$进行归纳，当$n' = 0'$时，$f(n) = 0'$，$f$的定义中规定$f(0) = 0'$，所以存在$n = 0 in NN$使得$f(0) = 0'$

      现在归纳的假设存在$n in NN$，使得$f(n) = n'$，接下来证明$n'++'$的情况下成立。

      $ f(n++) = n'++' = f(n)++' $由归纳假设$exists n in NN, f(n) = n'$，所以前式成立，因此存在$m = n++ in NN$，使得$f(m) = n'++'$，归纳结束
    
    - 综上，这样的$f$是双射，也因此，自然数系唯一
  ]
]

== 集合的基数

#definition(title: "相等的基数")[
  称集合$X,Y$有_相等的基数_当且仅当存在一个双射$f: X -> Y$
]

#definition[
  设$n$是一个自然数，称集合$X$的基数为$n$当且仅当$X$和集合${i in NN: 1<=i<=n}$有相同的基数。$X$有$n$个元素当且仅当$X$的基数为$n$
]

#note-block[
  上面的定义中，可以把${i in NN: 1 <= i <= n}$替换为${i in NN: i<n}$，因为他们有相等的基数

  #proof[

    令$X = {i in NN: i<n}, Y={i in NN: 1<= i <= n}$，函数$f: X->Y$定义为$f(x) = x++$，接下来证明$f$是双射

    - 单射
      
      由皮亚诺公理$++$函数是单射的，所以$forall x in NN, forall y in NN, f(x) = f(y) => x++ = y++ => x = y$，所以$f$是单射的

    - 满射

      $&forall y in Y => 1 <= y <= n$，根据皮亚诺公理，$y$一定是某个自然数的后继，令$y = x++$，由于$1 <= y <= n$，所以$0++ <= x++ <= n$，进而$0<=x<n, x in X$，由于$y = x++ = f(x)$，所以$forall y in Y, exists x in X, f(x) = y$
    
    - 综上，可以构造出双射函数$f:X->Y$，所以$X$和$Y$有相同的基数，所以在计算基数的时候可以替换了
  ]
]

#lemma[
  假设$n >= 1$，且$X$的基数为 $n$，那么$X$是非空的。$forall x in X,"集合"X without {x}$的基数是$n-1$

  #proof[
    - 由于$X$的基数为$n$，那么存在一个双射函数$f:X -> Y = {i in NN: 1<=i<=n}$，由于$n>=1$，那么$Y$非空，取$y = 1 in Y$，由于满射性，$ exists x in X, f(x) = 1$，所以$X$非空。

    - 由于$X$的基数为$n$，那么存在双射$f:X->{i in NN: 1<=i<=n}$

      定义一个函数$g:X without {x}-> {i in NN: 1<= i <=n-1}$，其中$x in X$，满足$forall y in X without {x}$ $ g(y)=cases(f(y)\, &f(y) < f(x), f(y)-1\, &f(y) > f(x)) $注意，$f(y) = f(x)$是不可能的，因为$f$是双射，那么$f(y) = f(x) => y = x$，而$y in X without {x}$，矛盾，所以$f(y)!=f(x)$，上面定义的分段函数是考虑了所有情况的。接下来只需要证明$g$在$X without {x}$上是双射即可。

      该分段函数在每一个分段上都是是双射的，所以$g:X without {x}:{i in NN: 1<=i <=n-1}$是双射函数，也即$X without {x}$的基数是$n-1$
  ]
]

#theorem("基数的唯一性")[
  集合$X$的基数为$n$，那么$X$不可能还有其他的基数，也即$forall m != n$，$m$不是$X$的基数
  #proof[
    对$n$进行归纳，当$n=0$时，集合$X=emptyset$，空集不会非0基数。假设$n$的情况下，集合有唯一基数成立，现在证明$n++$的情况。

    假设存在$m != n++$，$m$也是$X$的基数，由引理，$X$是非空的，且如果$x in X$，那么$X without {x}$的基数为$n$，同时也是$m-1$，由归纳假设$n = m - 1 => n++ = m$，矛盾，归纳完毕
  ]
]

#definition("有限集")[
  一个集合是有限的，当且仅当它的基数是某个自然数$n$，否则称之为无限的。如果$X$是一个有限集，记其基数为$\#(X)$.
]

#theorem("自然数集"+[$NN$]+"是无限的")[
  #proof[
    假设$NN$是有限集，那么令$\#(NN) = n$，于是存在一个双射$f:{i in NN: 1<=i<=n} -> N$，那么存在$M in NN$，使得$forall 1<=i<=n, f(i) <= M$，那么$forall 1<=i<=n, f(i) < M++$，所以$M++$无法被$f$映射到，这与满射是矛盾的。于是$NN$是无限集
  ]
]

#property[基数算术][
  
  + $X$是有限集，$x$是对象，且$x in.not X$，那么$X union {x}$是有限集且$\#(X union {x}) = \#(X)+1$
  
  + $X、Y$是有限集，那么$X union Y$是有限集，且 $\#(X union Y) <= \#(X) + \#(Y)$，且当$X inter Y = emptyset$时取等

  + $X$是有限集，集合$Y subset.eq X$，那么$Y$也是有限的。且$\#(Y)<=\#(X)$，如果$Y subset.neq X$，那么$\#(Y) < \#(X)$

  + $X$是有限集，且函数$f:X->Y$，那么$f(X)$是有限集，且满足$\#(f(X)) <= \#(X)$，当$f$是单射时，$\#(f(X)) = \#(X)$

  + $X、Y$都是有限集，那么$X times Y$也是有限的，且$\#(X times Y) = \#(X) times \#(Y)$

  + $X、Y$是有限集，那么$Y^X$是有限的，且 $\#(Y^X) = \#(Y)^(\#(X))$
]

#problem[证明基数相等是自反、对称和可传递的][
  $X、Y、Z$都是集合
]

#problem[证明$X = emptyset <=> \#(X) = 0$][]

#problem[自然数集的有限子集是有界的][]

#problem[证明基数运算][]

#problem[设$A、B$是集合，通过构造一个明确的双射来证明$\#(A times B) = \#(B times A)$，并利用基数算术证明乘法交换律][]

#problem[$A、B、C$都是集合，通过构造一个明确的双射来证明$\#((A^B)^C) = \#(A^(B times C))$，并类似的，证明$forall a, b, c in NN, (a^b)^c = a^(b c)$和$a^b times a^c = a^(b+c)$][]

#problem[$A、B$是集合，如果存在一个单射函数 $f: A -> B$，那么称A的基数小于等于B的基数，证明如果$A、B$都是有限集，那么$A$的基数小于等于$B$的基数，当且仅当$\#(A) <= \#(B)$][]

#problem[$A、B$都是集合，且存在一个单射函数$f:A->B$，证明也存在一个满射函数$g:B->A$][]

#problem[$A、B$是有限集，证明$A union B、A inter B$也是有限集，且$\#(A) + \#(B) = \#(A union B) + \#(A inter B)$][]

#problem[令$A_1, ..., A_n$是有限集，且满足$\#(union.big_(i in {1,...,n})A_i) > n$，证明存在$i in {1,...,n}$使得$\#(A_i) >= 2$，即抽屉/鸽巢原理][]