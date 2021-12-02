# Natural Numbers

In Lean, naturals are defined as an "inductive type". It then automatically gets the equivalents of PA1~PA5 and the Axiom of Recursion!

<details>
<summary>(Old content)</summary>

(The following descriptions are mainly in first-order logic; in Lean things are different.)

> [https://en.wikipedia.org/wiki/Peano_axioms#First-order_theory_of_arithmetic](https://en.wikipedia.org/wiki/Peano_axioms#First-order_theory_of_arithmetic)
>
> **Alphabet**
>
> - Constant symbols: $0$ (PA1)
> - Function symbols: $+$, $·$, $\nu()$ (PA2)
> - Predicate symbols: $=$
>
> **Abbreviations**
>
> - $1 := \nu(0)$  
>   $2 := \nu(1)$  
>   ...
> - $x\leq y := (\exists z, x + z = y)$
> - $x<y := (x\leq y \land x\neq y)$
>
> **Axioms**
>
> - $\forall x, \nu(x) \neq 0$ (PA3)
> - $\forall xy, \nu(x)=\nu(y)\rightarrow x=y$ (PA4)
> - (Schema) $\varphi(0)\land (\forall x, \varphi(x)\rightarrow\varphi(\nu(x)))\rightarrow \forall x,\varphi(x)$ (First-order PA5: Induction Schema)
> - (SOL) $\forall P, (P(0)\land(\forall x, P(x)\rightarrow P(\nu(x)))\rightarrow \forall x, P(x))$ (PA5: Axiom of Induction)
> - $\forall x, x+0=x$
> - $\forall xy, x + \nu(y) = \nu(x + y)$
> - $\forall x, x·0 = 0$
> - $\forall x, x · \nu(y) = x · y + x$

> **Theorem.** The *Axiom of Recursion*, $\forall Fx_0, \exists!R, (R(0)=x_0\land(\forall x,R\ \nu\ x = F\ R\ x)$, is equivalent to the *Axiom of Induction* given P1~P4.
>
> *Proof.* Induction ⇒ Recursion:
>
> - For any function $F: \mathbb{N}\rightarrow\mathbb{N}$ and $x_0\in\mathbb{N}$,
>   - Existence: [How to do this in FOL + ZFC?]
>   - Uniqueness: assume $R_1$ and $R_2$ both satisfy the two conditions.
>     - By induction we have $R_1(x)=R_2(x)$ for all $x\in\mathbb{N}$.
>     - So $R_1 = R_2$.
> - Now we have proved the Ax. Recursion.
>
> Recursion ⇒ Induction:
>
> - For any given predicate $P$,
>   - Assume that $P(0)$ and $\forall x, P(x)\rightarrow P(\nu(x))$ hold,
>     - Define function $R': \mathbb{N}\rightarrow\{0,1\}$ be such that $R'(x) = 1 \leftrightarrow \forall y\leq x, P(y)$.
>     - Then by assumption, $R'(0)=1$, and if $R'(x)=1$ then $R'(\nu(x))=1$ \[???\], while if $R'(x)=0$ then $R'(\nu(x)) = 0$.
>     - Since $R'(x)=0\lor R'(x)=1$, we have $R'(\nu(x))=R'(x)$ for all $x\in\mathbb{N}$.
>     - By the Ax. Rec. (let $F(x):=x$ for all $x\in\{0, 1\}$, and $x_0:=1$) we know that there is a unique $R$ such that $R(0)=1$ and $\forall x, R(\nu(x)) = R(x)$.
>     - The constant function $C(x):=1$ also satisfies the two conditions.
>     - So by uniqueness, $R'(x)=C(x)$ for all $x\in\mathbb{N}$.
>     - Then by definition of $R'$, $P(x)$ holds for all $x\in\mathbb{N}$.
> - Now we have proved the Ax. Induction. $\blacksquare$
>
> **Corollary.** The addition and multiplication functions are *uniquely defined* by their axioms (i.e. any function satisfying these axioms will be equal to the addition and multiplication functions). (Is it really a deduced result?)
>
> **Corollary.** $x+1 = \nu(x)$. (By definition)
>
> **Corollary.** For any $x$, either $x=0$ or $x=\nu(x')$ for some $x'$. (By induction)

</details>

[See Lean code]()

**Theorems.** Let $x,y,z\in\mathbb{N}$, then:

- (A1) $(x+y)+z=x+(y+z)$
- (A2) $0+x=x+0=x$
- (A3) $x+y=y+x$
- (M1) $(x·y)·z=x·(y·z)$
- (M2) $1·x=x·1=x$
- (M3) $x·y=y·x$
- (D) $(x+y)·z=x·z+y·z$

> This is a "field without inverses" (aka. "commutative semiring")

<details>
<summary>(Old content)</summary>

- (A1): Induction on $z$.
  - Base: $(x+y)+0 = x+y = x+(y+0)$.
  - Step: $(x+y)+\nu(z) = \nu((x+y)+z) =^{ih.} \nu(x+(y+z)) = x+\nu(y+z) = x+(y+\nu(z))$.
- (A2): Induction on $x$.
  - Base: $0+0 = 0+0 = 0$.
  - Step: $0+\nu(x)=\nu(0+x)=^{ih.}\nu(x)=\nu(x)+0$.
- (A3): Induction on $y$.
  - Base: $x+0=0+x$ (by A2).
  - Step: Induction on $x$.
    - Base: $0+\nu(y)=\nu(y)+0$ (by A2).
    - Step: $\nu(x)+\nu(y)=\nu(\nu(x)+y)=^{ih.y}\nu(y+\nu(x))=\nu(\nu(y+x))$ $=^{ih.y}\nu(\nu(x+y))=\nu(x+\nu(y))=^{ih.x}\nu(\nu(y)+x)=\nu(y)+\nu(x)$.
- (D) Induction on $z$.
  - Base: $(x+y)·0=0=0+0=x·0+y·0$.
  - Step: $(x+y)·\nu(z)=(x+y)·z+(x+y)=^{ih.}x·z+y·z+(x+y)$ $=(x·z+x)+(y·z+y)=x·\nu(z)+y·\nu(z)$.
- (M3) Induction on $y$.
  - Base: Induction on $x$.
    - Base: $0·0=0·0$.
    - Step: $\nu(x)·0=0=x·0=^{ih.x}0·x=0·x+0=0·\nu(x)$.
  - Step: Induction on $x$.
    - Base: $0·\nu(y)=0·y+0=^{ih.y}y·0+0=0=\nu(y)·0$.
    - Step: $\nu(x)·\nu(y)=\nu(x)·y+\nu(x)=^{ih.y}y·\nu(x)+\nu(x)=y·x+y+\nu(x)$ $=^{ih.y}x·y+y+x+1=x·\nu(y)+y+1=^{ih.x}\nu(y).x+\nu(y)=\nu(y)·\nu(x)$.
- (M2) Induction on $z$.
  - Base: $1·0=0=0+0=0·0+0=0·1$.
  - Step: $1·\nu(x)=1·x+1=^{ih.}x·1+1=(x·0+x)+1=(0+x)+1$ $=x+1=\nu(x)=\nu(x)·0+\nu(x)=\nu(x)+1$.
- (M1) Induction on $z$. (comm + distrib ⇒ distrib.r)
  - Base: $(x·y)·0=0=x·0=x·(y·0)$.
  - Step: $(x·y)·\nu(z)=(x·y)·z+(x·y)=^{ih}x·(y·z)+(x·y)=^{distrib.r}x·(y·z+y)$ $=^{unit}x·(y·z+y·1)=^{distrib.r}x·(y·(z+1))=^{succ}x·(y·\nu(z))$. $\blacksquare$

</details>

*Proof.* [See Lean code]()

**Theorems.** Let $x,y\in\mathbb{N}$. Then:

- **If $x+y=x$, then $y=0$.**
- **If $x+y=0$, then $x=y=0$.**
- **(CA) If $x+z=y+z$, then $x=y$.** (Weaker than negation)
- **(CM) If $x·z=y·z$ and $z\neq0$, then $x=y$.** (Weaker than inverse)

<details>
<summary>(Old content)</summary>

- (CA) Induction on $z$.
  - Base: $x+0=y+0\Rightarrow x=y$.
  - Step: $x+\nu(z)=y+\nu(z) \Rightarrow \nu(x+z)=\nu(y+z) \Rightarrow x+z=y+z \Rightarrow^{ih.} x=y$.
- ($x+y=x\rightarrow y=0$) $x+y=x\Rightarrow x+y=x+0\Rightarrow y=0$.
- ($x+y=0\rightarrow x=y=0$) Induction on $y$.
  - Base: $x+0=0\Rightarrow x=0=0$.
  - Step: $x+\nu(y)=0\Rightarrow \nu(x+y)=0\Rightarrow \bot \Rightarrow x=y=0$.
- (CM) Let $z'$ be such that $z=\nu(z')$.
  Induction on $x$.
  - Base: $0z=yz ⇒ 0=y\nu(z')=yz+y ⇒ yz=y=0=x$.
  - Step: $\nu(x)z=yz ⇒ yz=xz+z$.
    - If $y=0$, then $0=\nu(x)z=\nu(x)\nu(z') ⇒ \bot ⇒ y=\nu(x)$.
    - If $y=\nu(y')$, then $\nu(y')z=xz+z ⇒ y'z+z=xz+z ⇒^{ca.} y'z=xz$ $⇒^{ih.} y'=x ⇒ \nu(y')=\nu(x) ⇒ y = \nu(x)$. $\blacksquare$

**Definition.** Let $x,y\in\mathbb{N}$. We say that *$x$ is smaller than or equal to $y$* (Notation: $x\leq y$) iff there exists $v\in\mathbb{N}$ such that $y=x+v$. If additionally $v\neq 0$, we say that *$x$ is strictly smaller than $y$* (Notation: $x<y$).

**Corollary.** $x \leq y \leftrightarrow (x<y\lor x=y)$. // Proof: ⇒: by cases ($v=0$ or $v\neq 0$). ⇐: trivially by cases.

</details>

*Proof.* [See Lean code]()

**Theorem.** $\leq$ is a total order.

<details>
<summary>(Old content)</summary>

- Refl: for any $x$, $x+0=x$ so $x\leq x$.
- Antisymm: for any $x, y$ such that $x+c=y$ and $y+d=x$ for some $c, d$:
  - We have $x+c+d=x$ so $c+d=0$ so $c=d=0$ so $x=y$.
- Trans: for any $x,y,z$ such that $x+c=y$ and $y+d=z$ for some $c,d$:
  - $x+c+d=x+(c+d)=z$ so $x\leq z$.
- Total: for any $x$, induction on $y$:
  - Base: $0\leq x$.
  - Step: by cases:
    - When $x\leq y$ (i.e. $x+c=y$), we have $x+(c+1)=\nu(y)$ (i.e. $x\leq \nu(y)$).
    - When $y\leq x$ (i.e. $y+c=x$), by cases:
      - $c\neq 0$: $y+(\pi(c)+1)=x$ so $\nu(y)+\pi(c)=x$ (i.e. $\nu(y)\leq x$).
      - $c=0$: $y=x$ so $\nu(y)=x+1$ (i.e. $x\leq \nu(y)$). $\blacksquare$

</details>

*Proof.* [See Lean code]()

**Corollary.** Let $x,y,z\in\mathbb{N}$. Then:

- If $x\leq y$, then $x+z\leq y+z$.
- If $x\leq y$, then $x·z\leq y·z$.
- (Trichotomy) Either $x<y$, $y<x$ or $x=y$.

<details>
<summary>(Old content)</summary>

- $x\leq y$ means $x+c=y$ for some $c$ ⇒ $x+c+z=y+z$ ⇒ $(x+z)+c=y+z$ ⇒ $x+z\leq y+z$.
- $x\leq y$ means $x+c=y$ for some $c$ ⇒ $y·z=(x+c)·z=x·z+c·z$ ⇒ $x·z\leq y·z$.
- By totality of $\leq$, for any $x$ and $y$ there are three cases:
  - $x\leq y$ but $\lnot(y\leq x)$. So $x\neq y$ (refl). So $x<y$ (def).
  - $y\leq x$ but $\lnot(x\leq y)$. So $x\neq y$ (refl). So $y<x$ (def).
  - $x\leq y$ and $y\leq x$. So $x=y$ (antisymm). $\blacksquare$

</details>

*Proof.* [See Lean code]()

**Theorem.** (Induction with Non-zero Base) $\forall P,n_0, (P(n_0)\land(\forall x\geq n_0, P(x)\rightarrow P(\nu(x)))\rightarrow\forall x\geq n_0, P(x))$.

<details>
<summary>(Old content)</summary>

Let $P'$ be such that $P'(x)\leftrightarrow P(x+n_0)$ for all $x$.

Then by induction on $x$:

- Base: $P'(0)\leftrightarrow P(n_0)\leftrightarrow\top$.
- Step: if $P'(x)$, then $P(n_0+x)$, then $P(\nu(n_0 + x))$, then $P(n_0+\nu(x))$, then $P'(\nu(x))$.

Now $P'(x)$ holds for all $x$, i.e. $P(x)$ holds for all $x\geq n_0$. $\blacksquare$

</details>

*Proof.* [See Lean code]()

**Theorem.** (Principle of Strong Induction) $\forall P,n_0, (P(n_0)\land(\forall x, (\forall y,n_0\leq y\leq x\rightarrow P(y))\rightarrow P(\nu(x)))\rightarrow\forall x\geq n_0, P(x))$.

**Corollary.** Given P1~P4, the *Ax. Ind.* and the *Strong Ind.* are equivalent.

<details>
<summary>(Old content)</summary>

Let $P'$ be such that $P'(x)\leftrightarrow (\forall y, n_0\leq y\leq x\rightarrow P(y))$ holds.

Then by induction on $x$:

- Base ($x=n_0$): $P'(n_0)\Leftrightarrow(\forall y, n_0\leq y\leq n_0\rightarrow P(y))\Leftrightarrow(\forall y, y=n_0\rightarrow P(y))\Leftrightarrow P(n_0)$.
- Step ($x\geq n_0$): $P'(x)\Leftrightarrow (\forall y, n_0\leq y\leq x\rightarrow P(y))\Rightarrow P(\nu(x))$, so $\forall y, n_0\leq y\leq \nu(x)\rightarrow P(y)$ holds by trichotomy ($y \leq x$ or $y > x$), so $P'(\nu(x))$ holds.

Now $P'(x)$ holds for all $x\geq n_0$, so in particular $P(x)$ holds for all $x\geq n_0$. $\blacksquare$

</details>

*Proof.* [See Lean code]()

**Theorem.** (Well-ordering Principle) $\forall X, ((\exists a, a\in X)\rightarrow (\exists a\in X, \forall x\in X,a\leq x))$.

<details>
<summary>(Old content)</summary>

By classical contraposition:

- Assume that a subset $X$ has no least element.
  - By strong induction, prove $\forall x, x\notin X$:
    - Base: if $0\in X$, then $0$ is the least element ⇒ $\bot$.
    - Step: if $\nu(x)\in X$, then:
      - If there exists some $y\in X$ such that $y < \nu(x)$, then $y\leq x$, $\bot^{ih.}$.
      - So $\nu(x)\leq y$ for all $y\in X$.
      - So $\nu(x)$ is the least element ⇒ $\bot$.
    - So $\nu(x)\notin X$.
  - Now $X$ is empty.
- So if $X$ is nonempty, it must have a least element. $\blacksquare$

</details>

*Proof.* [See Lean code]()

> Note that this principle is NOT a replacement for Ax. Ind.! But given that $<$ is a strict total order, this principle is equivalent to the "strict version" of Principle of Strong Induction (aka. Transfinite Induction).



-----

# Integers

**Lemma.** The binary relation $(a,b)\sim(c,d)\leftrightarrow a+d=c+b$ is an equivalence relation on $\mathbb{N}^2$.

<details>
<summary>(Old content)</summary>

- Refl: $a+b=b+a$ gives $(a,b)\sim(a,b)$.
- Symm: if $(a,b)\sim(c,d)$ (i.e. $a+d=c+b$), then $c+b=a+d$ (i.e. $(c,d)\sim(a,b)$).
- Trans: if $(a,b)\sim(c,d)$ (i.e. $a+d=c+b$) and $(c,d)~(e,f)$ (i.e. $c+f=e+d$), then $a+(d+c)+f=e+(d+c)+b$, so $a+f=e+b$ by N-CA. $\blacksquare$

</details>

*Proof.* [See Lean code]()

**Definition.** The set of integers, $\mathbb{Z} := \mathbb{N}^2/\sim$, is **the set of all equivalence classes** $cl((a,b))$ under such an equivalence relation.

> The equivalance class $cl((a, b))$ is also denoted by $(a-b)$.

> `TODO: quotient structures in Lean`
