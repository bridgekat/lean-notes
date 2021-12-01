# Functions

**Notation.** $f: X\rightarrow Y$ denotes a function with domain $X$ and codomain $Y$.  
**Notation.** `f : X → Y` denotes a function with domain type `X` and codomain type `Y`.

> Note: "codomain" is not "image" (aka. "range")...

**Notation.** (Anonymous Functions) $x \mapsto x^2$ and $\lambda x. x^2$ are notations that represent the function $f(x)=x^2$ without giving it a name.  
**Notation.** (Anonymous Functions) All functions in Lean are written in the form of `(λ x, x ^ 2)`.

**Notation.** (Composition) If $f: A\rightarrow B$ and $g: B\rightarrow C$, $[g\circ f]$ is the function from $A$ to $C$: "first apply $f$, then apply $g$."  
**Notation.** (Composition) If `f : A → B` and `g : B → C`, then `(g ∘ f) : A → C`: "first apply `f`, then apply `g`."

**Proposition.** (Extensionality of Functions) Two functions $f:X\rightarrow Y$ and $g:X\rightarrow Y$ are **equal** iff $\forall x\in X, f(x) = g(x)$.  
**Proposition.** (Extensionality of Functions) [See Lean code]()

**Definitions.**

- A function $f: X \rightarrow Y$ is called **injective** iff $\forall a,b\in X, (f(a)=f(b)\rightarrow a=b)$.
- A function $f: X\rightarrow Y$ is called **surjective** iff $\forall y\in Y,\exists x\in X, f(x)=y$.
- A function $f: X\rightarrow Y$ is called **bijective** iff it is both injective and surjective.

*Formally,* [See Lean code]()

**Theorems.** Let $f: X\rightarrow Y$ and $g: Y \rightarrow Z$ be functions, and $[g\circ f]: X \rightarrow Z$ be the composition of $f$ and $g$. Then: 

- If $f$ and $g$ are **both injective, then so is $g\circ f$.**
- If $f$ and $g$ are **both surjective, then so is $g\circ f$.**
- If $f$ and $g$ are **both bijective, then so is $g\circ f$.**
- If $g\circ f$ is **injective, then so is $f$**.
- If $g\circ f$ is **surjective, then so is $g$**.

*Proof.* [See Lean code]()

**Definition.** Say $f: X\rightarrow Y$ is a function. We say that a function $g: Y\rightarrow X$ is a **two-sided inverse** of $f$, if **both** of the following are true:

- For all $x\in X$, $g(f(x))=x$;
- For all $y\in Y$, $f(g(y))=y$.

**Corollary.** $g$ is a two-sided inverse of $f$ iff $f$ is a two-sided inverse of $g$.

*Formally,* [See Lean code]()

> Note: $\sin^{-1}$ is not a two-sided inverse for $\sin: \mathbb{R}\rightarrow\mathbb{R}$, as $\sin^{-1}(\sin(x))$ is not always equal to $x$.

**Theorem.** A function $f: X\rightarrow Y$ **has a two-sided inverse iff it is a bijection**.

*Proof.*

- **If:** for each $y \in Y$, there is at most one (by injectivity) and at least one (by surjectivity) $x \in X$ such that $f(x) = y$, so we define $g(y) := x$. Then for all $x \in X$, $g(f(x)) = x$ by definition, and for all $y \in Y$ $f(g(y)) = y$ by definition.  
- **Only if:** let its inverse be $g:Y\rightarrow X$. Inj: for all $a, b \in X$, $f(a) = f(b) \Longrightarrow g(f(a)) = g(f(b)) \Longrightarrow a = b$. Surj: for all $y\in Y$, there is a $g(y)\in X$ such that $f(g(y))=y$. $\blacksquare$

*Proof.* [See Lean code]()


-----

# Relations

**Definition.** (Binary Relation) A binary relation on a set $X$ is a function $R: X^2\rightarrow Prop$.  
**Definition.** (Binary Relation) A binary relation on a type `X` is a function `R : X → X → Prop`.

> Predicate on (subset of) $X^2$, binary relation on $X$.

> Specifically, $\land$, $\lor$, $\rightarrow$, $\leftrightarrow$ are all binary relations on `Prop`.

**Definitions.** Let $R$ be a binary relation on a set $X$.

- $R$ is called **reflexive** iff $\forall x \in X, R(x, x)$.
- $R$ is called **symmetric** iff $\forall a,b \in X, R(a, b)\rightarrow R(b,a)$.
- $R$ is called **antisymmetric** iff $\forall a,b \in X, R(a, b)\land R(b,a)\rightarrow a=b$.
- $R$ is called **transitive** iff $\forall a,b,c \in X, R(a,b)\land R(b,c)\rightarrow R(a,c)$.
- $R$ is **total** iff $\forall a,b\in X, R(a,b) \lor R(b,a)$.

*Formally,* [See Lean code]()

**Definition.** Let $R$ be a binary relation on a set $X$.

- $R$ is a **partial order** iff $R$ is reflexive, antisymmetric, and transitive.
- $R$ is a **total order** iff $R$ is a partial order and $R$ is total.
- $R$ is an **equivalence relation** iff $R$ is reflexive, symmetric, and transitive.

*Formally,* [See Lean code]()

> Example: $\leftrightarrow$ can be seen as an equivalence relation on logical formulas.

> For an equivalence relation $R$, we may think it as a function $f: X\rightarrow V$ such that $R(a, b)$ holds iff $f(a) = f(b)$ (then $R$ is certainly reflexive, symmetric and transitive)...

**Definition.** Let $X$ be a set and let $\sim$ be an equivalence relation on $X$. Let $s\in X$ be an arbitrary element. We define the **equivalence class of $s$**, written $cl(s)$, to be the set of elements of $X$ which is related to. **That is, $cl(s) := \{x \in X\ |\ s\sim x\}$**.

*Formally,* [See Lean code]()

**Lemma.** Let $X$ be a set and let $\sim$ be an equivalence relation on $X$. Let $a, b\in X$. **If $a\sim b$ then $cl(b)\subseteq cl(a)$**.

*Proof.* For all $x\in cl(b)$, we have $b\sim x$; from transitivity of $\sim$ we have $a\sim x$, so $x\in cl(a)$. $\blacksquare$  
*Proof.* [See Lean code]()

**Lemma.** Let $X$ be a set and let $\sim$ be an equivalence relation on $X$. Let $a, b\in X$. **If $a\sim b$ then $cl(a) = cl(b)$**.

*Proof.* Directly from the last lemma and symmetry of $\sim$. $\blacksquare$  
*Proof.* [See Lean code]()

**Lemma.** Let $X$ be a set and let $\sim$ be an equivalence relation on $X$. Let $a, b\in X$. **If $\lnot (a\sim b)$ then $cl(a)\cap cl(b) = \emptyset$**.

*Proof.* By contraposition: if $x\in cl(a)$ and $x\in cl(b)$, then $a\sim x$ and $b\sim x$, then by symmetry & transitivity of $\sim$ we have $a\sim b$. $\blacksquare$  
*Proof.* [See Lean code]()

**Definition.** A *partition* of a set $X$ is **a set $A$ of non-empty subsets of $X$** with the property that **each element of $X$ is in *exactly one* of the subsets**.

*Formally,* [See Lean code]()

**Theorem.** Let $X$ be a set and let $\sim$ be an equivalence relation on $X$. Then **the set $V$ of equivalence classes $\{cl(x)\ |\ x\in X\}$ for $\sim$ is a partition of $X$**.

*Proof.* Every $v\in V$ is non-empty: $cl(x)$ must include $x$. For all $x\in X$, since $x\sim x$, we have $x\in cl(x)$ ($x$ is in at least one element of $V$), and if $x \in cl(y)$ for some $y\in x$ then $x\sim y$, then $cl(x) = cl(y)$ ($x$ is in at most one element of $V$). $\blacksquare$  
*Proof.* [See Lean code]()


**Theorem.** **Let $f: X\rightarrow V$ be defined by $f(x) := cl(x)$. Let $R_f$: $X^2\rightarrow Y$ such that $R_f(x, y)$ iff $f(x)=f(y)$. Then the equivalence relations $\sim$ and $R_f$ are equal.**

*Proof.* For all $a, b\in X$, **if $a \sim b$:** then $cl(a) = cl(b)$, then $f(a) = f(b)$ so $R_f(a, b)$; **if $R_f(a, b)$:** then $f(a) = f(b)$, then $cl(a) = cl(b)$, then $b\in cl(b) = cl(a)$ then $a\sim b$. $\blacksquare$  
*Proof.* [See Lean code]()

> The "partition from equivalence relation" and the "equivalence relation from partition" processes are inverses of each other. ⇒ Given a set, **there is a bijection between equivalence relations and partitions!**
