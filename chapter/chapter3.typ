#import "@preview/euler-math:0.1.0": *
#import "../utils/utils.typ" : *
= 集合论

== 基础知识

== 罗素悖论

== 函数

== 像与逆像

== 笛卡尔积

=== 正文
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
]
#proof[
  对$n$进行归纳。
  + $n=0$时，$i$取值为空，空真自动成立
  + $n=1$时，命题变为对于非空集合$X_1$，存在一个一元组$(x_1)$（或称对象$x_1$）$x_1 in X_1$，根据单个选取引理，如果集合非空，那么必然存在某个元素属于该集合，所以成立。
  + 现在归纳的假设在$n$的情况下成立。
  + 由于归纳假设，存在$(x_i)_(1<=i<=n)$，对于$forall 1<= i <= n$ 使得 $x_i in X_i$ 成立。在$n++$的情况下，由于$X_(n++)$非空，再次根据单个选取引理，一定存在对象 $a in X_(n++)$ ，现在令新的(n++)-元组为$(y_i)_(1<=i <= n++)$，其中$y_i = x_i, forall 1<= i <= n$ 且 $y_(i) = a, i = n++$ ，这样的(n++)-元组是存在的，所以$y_i in X_i, forall 1<= i <= n++$
  + 综上归纳完毕
]

=== 练习

#exercise[
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

#exercise[
定义一个有序$n$-元组是一个满射函数$x: {i in NN: 1<= i <= n} -> X$，其值域为任意集合$X$，将$x_i$写作$x(i)$，将$x$写作$(x_i)_(1 <= i <= n)$，验证$ (x_i)_(1 <= i <= n) = (y_i)_(1<=i<=n) <==> forall 1<= i <= n, x_i = y_i $
    #proof[
      + $(x_i)_(1 <= i <= n) = (y_i)_(1<=i<=n) ==> forall 1<= i <= n, x_i = y_i$
        
        函数$x$与函数$y$相等，那么$forall 1<= i <= n, x(i) = y(i)$，也即$forall 1<= i <= n, x_i = y_i$
      + $forall 1<= i <= n, x_i = y_i ==> (x_i)_(1 <= i <= n) = (y_i)_(1<=i<=n)$
        
        $forall 1<= i <= n, x_i = y_i$说明在定义域上两个函数逐点相等，那么函数$x$和函数$y$相等，那么根据定义$x = y ==> (x_i)_(1<=i<=n) = (y_i)_(1<=i<=n)$
    ]
]

#exercise[
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

#exercise[
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

#exercise[
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

#exercise[
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

#exercise[
  $X,Y$是集合，函数$pi_(X times Y -> X):X times Y -> X$被定义为$pi_(X times Y -> X)(x,y) = x$；函数$pi_(X times Y -> Y):X times Y -> Y$被定义为$pi_(X times Y -> Y)(x,y) = y$，这两个函数被称为定义在$X times Y$上的_坐标函数（co-ordinate functions）_，证明对于任意函数$f:Z -> X$和$g:Z -> Y$，存在唯一一个函数$h: Z -> X times Y$使得$pi_(X times Y -> X) compose h = f$和$pi_(X times Y -> Y) compose h = g$成立

  #proof[
    
    根据函数空间公理，记集合$H = (X times Y)^Z$为所有定义域为$Z$，值域为$(X times Y)$的函数的集合。根据题目要求，就是要证明集合${h in (X times Y)^Z: pi_(X times Y -> X) compose h = f and pi_(X times Y -> Y) compose h = g}$不为空集且只有一个元素。

    定义一个$pi_(X times Y ->X)$的一个偏函数为$pi'_(X times {y_0} -> X)$，其中$y_0 in Y$，根据定义$pi'_(X times {y_0} -> X)(x, y_0) = x$，易知$pi'_(X times {y_0}->X)$为双射函数。

  ]

]

#note-block[这样的函数$h$被称为$f"和"g$的_直和（direct sum）_，并记作_$h = f plus.o g$_]

#exercise[
  $X_1, ..., X_n$是集合，证明$product_(i=1)^n X_i = emptyset <==> exists 1<=i<=n,X_i = emptyset$
]

#exercise[
  $I,J$是集合，$forall alpha in I, A_alpha$是集合，$forall beta in J, B_beta$是集合，证明$(union.big_(alpha in I) A_alpha) inter (union.big_(beta in J)B_beta) = union.big_((alpha, beta) in I times J)(A_alpha inter B_beta)$
]

#exercise[
  $f:X->Y$是函数，定义函数$f$的_图（graph）_为$X times Y$子集，定义为${(x, f(x)):x in X}$，证明：对于$tilde(f):X -> Y"和"f:X->Y,f=tilde(f) <==> f, tilde(f)$有相同的图。如果集合$G subset.eq X times Y$，且$forall x in X$，集合${y in Y: (x, y) in G}$中只有一个元素，证明只有一个函数$f:X->Y$的图是$G$
]

#exercise[
  证明函数空间公理可以由幂集公理推出
]

#exercise(title: "严格的递归定义")[
  函数$f:NN times NN -> NN$，$c in NN$，证明存在一个函数$a: N -> N$，使得$ &a(0) = c  \  &a(n++) = f(n, a(n))，forall n in NN $成立，并且该函数是唯一的。进一步的，仅使用皮亚诺公理和集合论证明递归的定义
]

#exercise(title: "自然数系是唯一的")[
  假设有另一个“另类的”自然数系$NN'$，满足皮亚诺公理，证明存在一个双射$f: NN -> NN'$，满足$f(0) = 0' in NN'$，且$forall n in NN, forall n' in NN'$，有$f(n) = n' <==> f(n++) = n'++'$
]