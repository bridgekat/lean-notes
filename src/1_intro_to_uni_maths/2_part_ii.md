# Natural Numbers

> In Lean, naturals are defined as an "inductive type". It then automatically gets the equivalents of PA1~PA5 and the Axiom of Recursion!

**Theorems.** Let $x,y,z\in\mathbb{N}$, then:

- (A1) $(x+y)+z=x+(y+z)$
- (A2) $0+x=x+0=x$
- (A3) $x+y=y+x$
- (M1) $(x·y)·z=x·(y·z)$
- (M2) $1·x=x·1=x$
- (M3) $x·y=y·x$
- (D) $(x+y)·z=x·z+y·z$

> This is a "field without inverses" (aka. "commutative semiring")

**Theorems.** Let $x,y\in\mathbb{N}$. Then:

- **If $x+y=x$, then $y=0$.**
- **If $x+y=0$, then $x=y=0$.**
- **(CA) If $x+z=y+z$, then $x=y$.** (Weaker than negation)
- **(CM) If $x·z=y·z$ and $z\neq0$, then $x=y$.** (Weaker than inverse)

**Theorem.** $\leq$ is a total order.

**Corollary.** Let $x,y,z\in\mathbb{N}$. Then:

- If $x\leq y$, then $x+z\leq y+z$.
- If $x\leq y$, then $x·z\leq y·z$.
- (Trichotomy) Either $x<y$, $y<x$ or $x=y$.

**Theorem.** (Induction with Non-zero Base) $\forall P,n_0, (P(n_0)\land(\forall x\geq n_0, P(x)\rightarrow P(\nu(x)))\rightarrow\forall x\geq n_0, P(x))$.

**Theorem.** (Principle of Strong Induction) $\forall P,n_0, (P(n_0)\land(\forall x, (\forall y,n_0\leq y\leq x\rightarrow P(y))\rightarrow P(\nu(x)))\rightarrow\forall x\geq n_0, P(x))$.

**Corollary.** Given P1~P4, the *Ax. Ind.* and the *Strong Ind.* are equivalent.

**Theorem.** (Well-ordering Principle) $\forall X, ((\exists a, a\in X)\rightarrow (\exists a\in X, \forall x\in X,a\leq x))$.

> Note that this principle is NOT a replacement for Ax. Ind.! But given that $<$ is a strict total order, this principle is equivalent to the "strict version" of Principle of Strong Induction (aka. Transfinite Induction).



-----

# Integers

**Lemma.** The binary relation $(a,b)\sim(c,d)\leftrightarrow a+d=c+b$ is an equivalence relation on $\mathbb{N}^2$.

**Definition.** The set of integers, $\mathbb{Z} := \mathbb{N}^2/\sim$, is the set of all equivalence classes $cl((a,b))$ under such an equivalence relation.

> The equivalance class $cl((a, b))$ is also denoted by $(a-b)$.

**Lemma.** For any two equivalence classes $x$ and $y$:

- (ADD) There is a **unique class $z$ such that $\exists (a,b)\in x, \exists (c,d)\in y, (a+c, b+d)\in z$. Define $x+y:=z$**.
- (NEG) There is a **unique class $z$ such that $\exists (a,b)\in x, (b,a)\in z$. Define $(-x):=z$. Define $x-y := x+(-y)$**.
- (MUL) There is a **unique class $z$ such that $\exists (a,b)\in x, \exists (c,d)\in y, (ac+bd,ad+bc)\in z$. Define $xy := z$.**

> In Lean, we first define $(a, b) + (c, d) := (a + c, b + d)$, etc. and then check that this function **respects the equivalence relation:** for all $x\sim x'$ and $y\sim y'$, we have $x + y \sim x' + y'$.

**Definition.** Let $(a-b),(c-d)\in\mathbb{Z}$. We say that $(a-b)\leq (c-d)$ iff $a+d\leq c+b$ (i.e. there is a natural number $k$ such that $a+d+k=c+b$).

**Theorem.** An *isomorphism* of $\mathbb{N}$ to a subset of $\mathbb{Z}$, $\{cl((x,0))\ |\ x\in\mathbb{N}\}$, is given by $f(x):=cl((x,0))$.

> As a result, sometimes we say that $\mathbb{N}$ *is* a subset of $\mathbb{Z}$. [?]

**Theorem.** Every element $x\in\mathbb{Z}$ satisfies the condition that either $x\in\mathbb{N}$ or $(-x)\in\mathbb{N}$. If both conditions are satisfied, $x=0$.

> Therefore, we can denote $\mathbb{Z}=\{\ldots,-3,-2,-1,0,1,2,3,\ldots\}$.

**Theorems.** Let $x,y,z\in\mathbb{Z}$, then:

- (A1) $(x+y)+z=x+(y+z)$
- (A2) $0+x=x+0=x$
- (A3) $(-x)+x=x+(-x)=0$ **(supercedes CA)**
- (A4) $x+y=y+x$
- (M1) $(x·y)·z=x·(y·z)$
- (M2) $1·x=x·1=x$
- (M3) $x·y=y·x$
- (D) $(x+y)·z=x·z+y·z$

> This is a "field without multiplicative inverses" (aka. "commutative ring")

- (CM) If $x·z=y·z$ and $z\neq0$, then $x=y$.

> From now on we can feel free to use addition, subtraction and multiplication with all their rules as you know them.



-----

# Rationals

**Lemma.** The binary relation $(a,b)\sim(c,d)\leftrightarrow ad=cb$ is an equivalence relation on $\mathbb{Z}\times(\mathbb{Z}\setminus\{0\})$.

**Definition.** The set of rationals, $\mathbb{Q} := \mathbb{Z}\times(\mathbb{Z}\setminus\{0\})/\sim$, is **the set of all equivalence classes $cl((a,b))$ under such an equivalence relation**.

> The equivalance class $cl((a, b))$ is also denoted by $\dfrac{a}{b}$. So we have e.g. $\dfrac{1}{2}=\dfrac{3}{6}$.

**Lemma.** For any two equivalence classes $x$ and $y$:

- (ADD) There is a **unique class $z$ such that $\exists (a,b)\in x, \exists (c,d)\in y, (ad+cb, bd)\in z$. Define $x+y:=z$**.
- (NEG) There is a **unique class $z$ such that $\exists (a,b)\in x, (-a,b)\in z$. Define $(-x):=z$. Define $x-y := x+(-y)$**.
- (MUL) There is a **unique class $z$ such that $\exists (a,b)\in x, \exists (c,d)\in y, (ac,bd)\in z$. Define $xy := z$.**
- (INV) **If $(0,1)\notin x$**, then **there is a unique class $z$ such that $\exists (a,b)\in x, (b,a)\in z$. Define $z^{-1}:= z$. Define $\frac{x}{y} := xy^{-1}$**.

**Definition.** Let $\frac{a}{b},\frac{c}{d}\in\mathbb{Q}$. Assuming $b,d>0$ [?], #####

**Theorem.** An isomorphism of $\mathbb{Z}$ to a subset of $\mathbb{Q}$, $\{cl((x,1))\ |\ x\in\mathbb{Z}\}$, is given by $f(x):=cl((x,1))$.

> As a result, sometimes we say that $\mathbb{Z}$ *is* a subset of $\mathbb{Q}$. [?]

**Theorems.** Let $x,y,z\in\mathbb{Q}$, then:

- (A1) $(x+y)+z=x+(y+z)$
- (A2) $0+x=x+0=x$
- (A3) $(-x)+x=x+(-x)=0$
- (A4) $x+y=y+x$
- (M1) $(x·y)·z=x·(y·z)$
- (M2) $1·x=x·1=x$ where $1\neq 0$
- (M3) $x^{-1}·x=x·x^{-1}=1$ if $x\neq 0$ **Supercedes (CM)**
- (M4) $x·y=y·x$
- (D) $(x+y)·z=x·z+y·z$

> This is a "field"!

> From now on we can feel free to use addition, subtraction, multiplication and division with all their rules as you know them.
