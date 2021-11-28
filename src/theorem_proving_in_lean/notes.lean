/-
**Useful resources:**

* Theorem Proving in Lean: https://leanprover.github.io/theorem_proving_in_lean/
* Mario Carneiro's thesis: https://github.com/digama0/lean-type-theory/releases
* The HoTT Book: https://homotopytypetheory.org/book/
-/

/-
"Expressions" are formally strings (or "trees") of symbols.
Every expression **has a unique "type"**, which is **also an expression**. (The uniqueness is guaranteed by the "typing rules".)
You may imagine there is a "typing function" that maps all expressions to a subset of expressions.
*(Strictly speaking, a type should be a equivalence class of "judgmentally equivalent" expressions...)*

The "typing rules" guarantee that there are three different kinds of expressions:

* "Universe expr." are in the form of `Prop` or `Type n`; they could appear on both sides of `:`. They are a special kind of type exprs.
* "Type expr." have a universe expr. as its type. They could appear on both sides of `:`.
* "Term expr." are not type exprs. themselves, but have a type expr. as its type. They could only appear on the left of `:`.
* There are no other kinds of expressions.

We will now abbreviate "universe expression", "type expression" and "term expression" as "universe", "type" and "term", respectively.
Note the difference between "X is a type (expression)" and "X is of type Y" / "X has type Y"!

"Typing rules" are like "inference rules" in other formal logical systems, although apparently they just assign types to expressions;
A expression is *well-formed* if and only if it can be *assigned a type* according to these rules!

* A type α is called "inhabited" if there is an expression that gets assigned α as its type.

"Contexts" are essentially "lists of things in the form of `x : α`" (where `x` and `α` are expressions)
(plus a constraint: each thing must be "derivable" from previous ones using the typing rules...)

* We may understand each "thing" as a typing judgment (i.e. introduce a parameter `x` that has type `α`),
  or as an "assumption" (i.e. assume that type `α` is inhabited by something, and we call it `x`).
* With different lists of assumptions, the set of well-formed expressions varies.
-/

--------------------------------------------------------------------------------
-- **Structural rules**
-- (universe axioms, well-formed contexts, parameter, weakening)

universe u -- "The identifier `u` now denotes a 'universe level' (i.e. `Type u` will now be a well-formed universe)"

-- Check if an expression is well-formed (given the current context Γ) and output their type
-- Syntax: `#check <expr>`
#check Type u -- `Γ ⊢ (Type u : Type (u+1))` by U-formation rule
#check Prop   -- `Γ ⊢ (Prop : Type 0)` by "Prop-formation" rule (Lean only)

section -- "Push context (i.e. the list of assumptions)"

  -- Make some temporary assumptions (syntax: `parameter <identifier> : <type-expr>`)
  parameter α : Type u -- "The context Γ is now extended with `α : Type u`, after checking that `Type u` is a well-formed type."
  parameter β : Type 3 -- "The context Γ is now extended with `β : Type 3`, after checking that `Type 3` is a well-formed type."
  parameter v : α      -- "The context Γ is now extended with `v : α`, after checking that `α` is a well-formed type."
  parameter w : β      -- ...

  #check v -- `Γ ⊢ (v : α)` by structural rule
  #check w -- `Γ ⊢ (w : β)` by structural rule
  #check β -- `Γ ⊢ (β : Type 3)` by structural rule
  #check Type 3 -- `Γ ⊢ (Type 3 : Type 4)` by U-formation rule
  #check Type 4 -- `Γ ⊢ (Type 4 : Type 5)` by U-formation rule
  -- ...

end -- "Pop context"

-- When writing programs, we keep in mind the type of each expression;
-- When writing in Lean, we keep in mind the type of each expression *and* which universe that type lives in...
-- (Or do we? Ask at next Xena Thursday meeting) (Response: we do!)
-- This may need some time to get used to...

section pi_and_sigma_types -- "Push context, while assigning a name to the section (for decoration)"

--------------------------------------------------------------------------------
-- **Π-formation**

parameter α : Type 3     -- "The context Γ is now extended with `α : Type 3`..."
parameter β : α → Type 3 -- "The context Γ is now extended with `β : α → Type 3`, after checking that `α → Type 3` is a well-formed type."
-- Note: `α → Type 3` is just a synonym for `Π (x : α), Type 3`
-- Note: `α → Type 3` is well-formed type because the following (Π-formation rule) holds:
--   "if we extend Γ with `x : α`, then `Type 3` is a well-formed type (trivially)."

-- Derived rule (→-formation): if `α` and `β` are well-formed types, then so is `α → β` (just like in STT!).

section
  parameter x : α -- "If we extend the context Γ with assumption `x : α`..."
  #check β x      -- "...then `Γ ⊢ (β x : Type 3)`."
end

parameter f : Π (x : α), β x -- "The context Γ is now extended with `f : ...`, after checking... well-formed type..."
-- Note: `f : Π (x : α), β x` is well-formed type because the following (Π-formation rule) holds:
--   "if we extend Γ with `x : α`, then `β x` is a well-formed type (written `Γ, (x : α) ⊢ (β x : Type 3)`)."

-- Note: `β` produces a type `β x` given a term `x` of another type `α` ("type constructor from term");
--       `f` produces a term of type `β x` given a term `x` of another type `α` ("dependently-typed function").
-- Note: "type former" is a synonym for "type constructor"...

#check (Π (x : α), β x) -- `Γ ⊢ (Π (x : α), β x : Type 3)` (Π-formation rule also assigns a type for this type expression.)
-- Note: in general, the assigned universe level will be the maximum of the universes containing `α` and `β x` resp.
-- But if `β x : Prop`, there will be an exception (Lean only)...


-- **Π-introduction**

section
  parameter x : α -- "If we extend the context Γ with assumption `x : α`..."
  #check f x      -- "...then `Γ ⊢ (f x : β x)`."
end

#check λx, f x -- This expression containing "lambda" is well-formed and has type `Π (x : α), β x`
-- Note: `Γ ⊢ ((λx, f x) : Π (x : α), β x)` because the following (Π-introduction rule) holds:
--   "if we extend Γ with `x : α`, then `Γ ⊢ (f x : β x)` (i.e. `f x` is a term of type `β x`)"

-- Note: here the expression `f x` could be any expression that possibly contains `x`!
--       if its type does not contain `x`, we go back to the non-dependent case where `Π` can be abbreviated as `→`.

-- Derived rule (→-introduction): if extending Γ with `x : α` could result in `Γ ⊢ (f x : β)`, then `Γ ⊢ ((λx, f x) : α → β)`.


-- **Π-elimination**

def g := (λx, f x) -- Define a synonym for (λx, f x),
#check g           -- It has type `Π (x : α), β x`.

parameter t : α -- Now we add assumption `t : α` to the context Γ.

#check g t -- This expression containing two successive terms (the first one contains lambda) is well-defined
-- Note: `Γ ⊢ g t : β t` because the following (Π-elimination rule) holds:
--   "if `Γ ⊢ (g : Π (x : α), β x)` and `Γ ⊢ (t : α)`, then `Γ ⊢ (g t : β t)` (i.e. `g t` is a term of type `β t`)"

-- Since `α → β` is a synonym for `Π (x : a), β`, we have:
-- Derived rule (→-elimination): "if `Γ ⊢ (g : α → β)` and `Γ ⊢ (t : α)`", then `Γ ⊢ (g t : β)`.


-- **Π-computation** and **Π-uniqueness**

#check (λx, f x) t
-- What we have done was using Π-introduction to introduce `(λx, f x)`, but after that
-- immediately use Π-elimination to obtain `(λx, f x) t : β t`.
-- This is for illustrative purpose (exhibit Π-introduction and Π-elimination rules), but
-- unnecessary in practice, since we may construct a term of type `β t` direcly using `f t`.
-- Lean has a mechanism to detect and simplify such detours.

-- Reduce `(λx, f x) t` to `f t` using the Π-computaion rule:
-- Syntax: `#reduce <expr>`
#reduce (λx, f x) t

-- *We should have another rule called "Π-uniqueness":*
#reduce (λx, f x) -- ??? (TODO: why this does not eta-reduce...)

-- If we view these expressions containing λ as functions...
-- (TODO: complete this part)

-- Note: "λ-abstraction" is "Π-introduction" in MLTT.
--       "λ-application" is "Π-elimination" in MLTT.
--       "β-reduction" is "Π-computation" in MLTT (also "cut-elimination" in natural deduction)
--       "η-reduction" is "Π-uniqueness" in MLTT.

-- If one expression could be "reduced" to another using the so-called "computation rules",
-- we say that the two expressions are "judgmentally equal" or "definitionally equal".
-- This equality (denoted as `≡`) is defined (by the set of "computation rules") to be an
-- equivalence relation over expressions.


--------------------------------------------------------------------------------
/-
It looks like the Σ type constructor is not a primitive notion in Lean, despite it being primitive in MLTT...
Nevertheless, I have taken a look first at how the MLTT rules for Σ are expressed in Lean.

(These sections (until inductive types) may be skipped; I made these notes just to familiarise myself with Lean and MLTT,
 and to "decrypt" the symbols appearing in the Appendix A of *The HoTT Book*...)
(Maybe unifying these types is a motivation of the design of inductive types?)
-/

-- **Σ-formation**

section
  parameter x : α -- ...
  #check β x      -- ...
  -- We may also write `Γ, (x : α) ⊢ (β x : Type 3)` for this.
end

#check (Σ (x : α), β x)
-- Note: `Γ ⊢ (Σ (x : α), β x : Type 3)` because the following (Σ-formation rule) holds:
--   `Γ, (x : α) ⊢ (β x : Type 3)` (i.e. `β x` is well-formed type given `x : α`)
-- Here `β x` can be replaced by arbitrary expression possibly containing `x`.

parameter β' : Type 7

#check Σ (x : α), β'
#check α × β'
-- Note: in MLTT, `α × β'` is a synonym for `Σ (x : α), β'` (although they are different here in Lean!)
-- Derived rule (×-formation): if `α` and `β` are well-formed types, then so is `α × β`.


-- **Σ-introduction**

parameter a : α
parameter b : β a

section
  parameter x : α
  #check β x
  -- `Γ, (x : α) ⊢ β x : Type 3`
end

#check sigma.mk a b
-- Note: `Γ ⊢ (⟨a, b⟩ : Σ (a : α), β a)` because the following (Σ-introduction rule) holds:
--   `Γ, (x : α) ⊢ β x : Type 3` (the Σ type is well-formed), and
--   `Γ ⊢ a : α`                 (premise), and
--   `Γ ⊢ b : β a`               (premise).
-- Here `β x` can be replaced by arbitrary expression possibly containing `x`.

parameter b' : β'
#check (a, b')
-- Derived rule (×-introduction): if `Γ ⊢ a : α` and `Γ ⊢ b : β`, then `Γ ⊢ (a, b) : α × β`.


-- **Σ-elimination**

-- Now assume a type constructor that takes the Σ type as parameter and produces a type
parameter γ : (Σ (x : α), β x) → Type 3
-- And a dependently-typed function that, given any element of the Σ type, produces a term of the type constructed above
parameter h : Π (x' : Σ (x : α), β x), γ x'

section
  parameter z : Σ (x : α), β x
  #check γ z
  -- `Γ, (z : Σ (x : α), β x) ⊢ (γ z : Type 3)` (check well-formed)
end

section
  parameter x : α
  parameter y : β x
  #check h (sigma.mk x y)
  -- `Γ, (x : α), (y : β x) ⊢ (h ⟨x, y⟩ : γ ⟨x, y⟩)` (check minor premise)
end

parameter p : Σ (x : α), β x -- (create major premise)

def g' (x : α) (y : β x) : γ ⟨x, y⟩ := h (sigma.mk x y)
#check g'
#check (λx, λy, g' x y) p.fst p.snd
-- Note: in MLTT, one reaches `Γ ⊢ (_ : (γ p))` because the following (Σ-elimination rule) holds:
--   `Γ, (z : Σ (x : α), β x) ⊢ (γ z : Type 3)`   (the γ(z) type is well-formed), and
--   `Γ ⊢ (p : Σ (x : α), β x)`                   (major premise), and
--   `Γ, (x : α), (y : β x) ⊢ (g x y : γ ⟨x, y⟩)` (minor premise).
-- Here `β x` (resp. `γ p`) can be replaced by arbitrary expression possibly containing `x` (resp. `p`).

-- In Lean, it seems like there is no "direct" method to obtain the conclusion from the premises above;
-- instead, by applying Π-introduction rule twice:
--   0. `Γ, (x : α), (y : β x) ⊢ (g x y : γ ⟨x, y⟩)`
--   1. `Γ, (x : α) ⊢ (λy, g x y : Π (y : β x), γ ⟨x, y⟩)`
--   2. `Γ ⊢ (λx, λy, g x y : Π (x : α), Π (y : β x), γ ⟨x, y⟩)`
-- we get a dependently-typed function that accepts the first and the second element of p [!],
-- and produces a term of type (γ p). In Lean we may use `p.fst` (`p.1`) and `p.snd` (`p.2`) to obtain the two elements of p.
#check p.fst
#check p.snd
#reduce (λ (x : α), β x) p.fst
-- (Here we may notice that the "uniqueness" of an expression's type is "under the equivalence relation `≡`"...)

-- Derived rule (×-elimination): if all three hold:
--   `Γ, (z : α × β) ⊢ (γ z : Type 3)`
--   `Γ ⊢ (p : α × β)`
--   `Γ, (a : α), (b : β) ⊢ (g x y : γ (x, y))`
-- Then one could obtain `Γ ⊢ (_ : γ p)` similarly.
-- In MLTT, this could be used "implement" `.fst` and `.snd`. (In Lean we already had them!)

-- (Since Sigma type is not a primitive notion, its rules are all derived;
--  TODO: Σ-computation rule)


end pi_and_sigma_types
section coproduct_type_and_0_and_1

--------------------------------------------------------------------------------
/-
By the Curry-Howard correspondence:
* `Π` is like `∀`;
* `→` is like `→`;
* `Σ` is like `∃`;
* `×` is like `∧`;
Now we are introducing the "coproduct type" `+`, or `∨`.
Then there is `0` for `⊥`, `1` for `⊤`, and finally `¬` is a synonym for `→ ⊥`.

Again, the coproduct type is not a primitive notion in Lean (despite it being primitive in MLTT).
-/

-- **+-formation**

parameter α : Type 3 -- ...
parameter β : Type 7 -- ...

#check α ⊕ β -- `Γ ⊢ (α ⊕ β : Type 7)`


-- **+-introduction**

section
  parameter a : α
  #check @sum.inl α β a
  -- `Γ, (a : α) ⊢ (sum.inl a : α ⊕ β)`
end

section
  parameter b : β
  #check @sum.inr α β b
  -- `Γ, (a : α) ⊢ (sum.inr b : α ⊕ β)`
end


-- **+-elimination**

-- These below can be arbitrary expressions with the correct types.
parameter γ : α ⊕ β → Type 9
parameter c : Π (x : α), γ (sum.inl x)
parameter d : Π (y : β), γ (sum.inr y)

section
  parameter z : α ⊕ β
  #check γ z
  -- `Γ, (z : α ⊕ β) ⊢ (γ z : Type 9)` (γ(z) is well-formed type)
end

section
  parameter x : α
  #check c x
  -- `Γ, (x : α) ⊢ (c x : γ (sum.inl x))` (check minor premise)
end

section
  parameter y : β
  #check d y
  -- `Γ, (y : β) ⊢ (d y : γ (sum.inr y))` (check minor premise)
end

parameter e : α ⊕ β -- (create major premise)

def g'' : Π (p : α ⊕ β), γ p
  | (sum.inl x) := c x 
  | (sum.inr y) := d y
#check g'' e
-- Note: in MLTT, one reaches `Γ ⊢ (_ : (γ e))` because the following (+-elimination rule) holds:
--   `Γ, (z : α ⊕ β) ⊢ (γ z : Type 9)` (the γ(z) type is well-formed), and
--   `Γ ⊢ (e : α ⊕ β)`                    (major premise), and
--   `Γ, (x : α) ⊢ (c x : γ (sum.inl x))` (minor premise 1), and
--   `Γ, (y : β) ⊢ (d y : γ (sum.inr y))` (minor premise 2).

-- In Lean, it seems like there is no "direct" method to obtain the conclusion from the premises listed above;
-- instead, by "pattern matching" on `p : α ⊕ β` like the `g''` defined above (this uses a "recursor" behind the scenes?),
-- we get a dependently-typed function that accepts both "variants" of `p` [!] and produces a term of type (γ p).


--------------------------------------------------------------------------------
-- **0-formation** and **0-elimination** (no introduction!)
-- In Lean, the empty type is `empty`. It is not a primitive notion... It is defined using `inductive`...

#check empty -- The 0-formation rule: `empty` is a well-formed type.

-- Assume a random type and a random type constructor
parameter δ : Type 12
parameter ε : empty → Type 17

section
  parameter x : empty
  #check ε x -- `Γ, (x : empty) ⊢ (ε x : Type 17)` (`ε(x)` is a well-formed type given `x : false`)
end

parameter a : empty -- (create major premise)

-- The 0-elimination rule:
#check @empty.rec (λ x, δ) a -- We can make a term that has type `δ` (i.e. we can make a term for any type we like!)
#check @empty.rec (λ x, ε x) a -- We can make a term that has type `ε(a)`


--------------------------------------------------------------------------------
-- **1-formation**, **1-introduction** (no elimination in Lean!)
-- In Lean, the unit type is `unit`. It is not a primitive notion... It is defined using `inductive`...

#check unit -- The 1-formation rule: `unit` is a well-formed type.

#check () -- The 1-introduction rule: `Γ ⊢ (() : unit)`.
-- The symbol `()` is a synonym for `unit.star`.

/-
-- Assume a random type constructor
parameter ζ : unit → Type 23
-- Assume that `z` has the type constructed by feeding `ζ` with `unit.star`
parameter z : ζ ()
-- Assume that `u` has unit type
parameter u : unit

*Oops, it seems that there is no 1-elimination rule in Lean...?*
*(But Lean has the "proof-irrelevance" rule!)*

-- Every `a` that has unit type could be used to replace the `star` in a type constructor;
--   the resulting new type will be inhabited if the original one is inhabited.
-- Every proof of `T` could be used to replace the proof `star` in a proposition;
--   the new proposition will have a proof if the original one does.
-/


end coproduct_type_and_0_and_1

--------------------------------------------------------------------------------
/-
Summary: only Π (and →) is a primitive notion in Lean. Σ, ×, +, 0, 1, ¬ are not.
（以下假设cumulative... 若依赖的两个type所在的universe level不等，Lean会在两者之间取最大值作为形成的type所在的level）

-- **Summary of formation rules:**
-- (i.e. how to make new *types*, mostly from existing ones)

Π-formation:
If   `Γ          ⊢ (α               : Sort n)`
     `Γ, (x : α) ⊢ (β(x)            : Sort n)`
Then `Γ          ⊢ (Π (x : α), β(x) : Sort n)`

Σ-formation:
If   `Γ          ⊢ (α               : Sort n)`
     `Γ, (x : α) ⊢ (β(x)            : Sort n)`
Then `Γ          ⊢ (Σ (x : α), β(x) : Sort n)`

→-formation:
If   `Γ          ⊢ (α     : Sort n)`
     `Γ          ⊢ (β     : Sort n)`
Then `Γ          ⊢ (α → β : Sort n)`

×-formation:
If   `Γ          ⊢ (α     : Sort n)`
     `Γ          ⊢ (β     : Sort n)`
Then `Γ          ⊢ (α × β : Sort n)`

+-formation:
If   `Γ          ⊢ (α     : Sort n)`
     `Γ          ⊢ (β     : Sort n)`
Then `Γ          ⊢ (α ⊕ β : Sort n)`

0-formation:
     `Γ          ⊢ (empty : Sort 1)` (But we can make it universe-polymorphic?)

1-formation:
     `Γ          ⊢ (unit  : Sort 1)` (But we can make it universe-polymorphic?)


-- **Summary of introduction rules**
-- (i.e. how to make new *terms*, mostly from existing ones)

Π-introduction:
If   `Γ, (x : α) ⊢ (b(x) : β(x))`
Then `Γ          ⊢ (λ x, b(x) : Π (x : α), β(x))`

Σ-introduction:
If   `Γ          ⊢ (a : α), (b : β(a))`
Then `Γ          ⊢ ((a, b) : Σ (x : α), β(x))` (resultant type must be well-formed)

→-introduction:
If   `Γ, (x : α) ⊢ (b(x) : β)`
Then `Γ          ⊢ (λ x, b(x) : α → β)`

×-introduction:
If   `Γ          ⊢ (a : α), (b : β)`
Then `Γ          ⊢ ((a, b) : α × β)`

+-introduction-left:
If   `Γ          ⊢ (a : α)`
Then `Γ          ⊢ (sum.inl a : α ⊕ β)` (resultant type must be well-formed)

+-introducton-right:
If   `Γ          ⊢ (b : β)`
Then `Γ          ⊢ (sum.inr b : α ⊕ β)` (resultant type must be well-formed)

1-introduction:
     `Γ          ⊢ (() : unit)`


-- **Summary of elimination rules**
-- (i.e. how to *use existing terms* to create new terms)

Π-elimination:
If   `Γ          ⊢ (f : Π (x : α), β(x))`
     `Γ          ⊢ (a : α)`
Then `Γ          ⊢ (f a : β(a))`

→-elimination:
If   `Γ          ⊢ (f : α → β)`
     `Γ          ⊢ (a : α)`
Then `Γ          ⊢ (f a : β)`

Σ-elimination:
If   `Γ                      ⊢ (p : Σ (x : α), β(x))`
     `Γ, (a : α), (b : β(x)) ⊢ (f a b : γ (a, b))`
Then `Γ                      ⊢ (... : γ p)` (type constructor γ must be well-formed)

×-elimination:
If   `Γ                   ⊢ (p : α × β)`
     `Γ, (a : α), (b : β) ⊢ (f a b : γ (a, b))`
Then `Γ                   ⊢ (... : γ p)`    (type constructor γ must be well-formed)

+-elimination:
If   `Γ          ⊢ (p : α ⊕ β)`
     `Γ, (a : α) ⊢ (f(a) : γ (sum.inl a))`
     `Γ, (b : β) ⊢ (g(b) : γ (sum.inr b))`
Then `Γ          ⊢ (... : γ p)`             (type constructor γ must be well-formed)

0-elimination:
     `Γ, (e : empty) ⊢ (... : γ e)`         (type constructor γ must be well-formed)

(The γ's here can be seen as "typing functions" -- these will be made clear in "inductive-elimination"...)
-/


section inductive_types

--------------------------------------------------------------------------------
/-
As mentioned before, in Lean, only the Π type constructor is a primitive notion.
Actually, Lean's primitive types merely include the **universes**, the **Π(Pi) type** and the **inductive types**.
Every other type or type constructor is built from these!

My intuition:

* "Universes" together form a "big chain" (or "concentric circles" if you prefer); types are those nodes "directly" attached to it.
* "Inductive typing" is used to make types (and terms for those types).
* "Pi type constructor" is used to make functions between types, and functions that can "target" different types (in the same universe).

Without inductive types, one could only play with universes and functions -- so boring...
-/

-- **Inductive-formation** and **inductive-introduction**

-- Enumerated type
inductive weekday : Type
| sunday    : weekday
| monday    : weekday
| tuesday   : weekday
| wednesday : weekday
| thursday  : weekday
| friday    : weekday
| saturday  : weekday

-- Make some terms of the above type...
#check weekday.sunday
#check weekday.monday
section
  open weekday
  #check sunday
  #check monday
end

-- "Advanced" enumerated type (aka. "algebraic data types"?)
inductive maybe_int : Type
| nothing :       maybe_int
| just    : int → maybe_int

-- Make some terms of the above type...
section
  open maybe_int
  #check nothing
  #check just 1
end

-- "Recursive" type!
inductive tree_int : Type
| leaf : int                       → tree_int
| node : tree_int → int → tree_int → tree_int

-- Make some terms of the above type...
section
  open tree_int
  #check leaf 1
  #check node (leaf 1) 2 (leaf 3)
  #check node (node (leaf 1) 2 (leaf 3)) 4 (leaf 5)
end

-- Type constructors (takes some arguments and produces a type)
-- (aka. type formers)
inductive maybe (α : Type) : Type
| nothing :     maybe
| just    : α → maybe

/-
The above definition is the same as:
`section`
`  parameter (α : Type)`
`  inductive maybe : Type`
`  | nothing :     maybe`
`  | just    : α → maybe`
`end`
(i.e. the `(α : Type)` is just some additional thing to be temporarily put into the context...)
(TODO: how does Lean modify definitions when the context is popped...?)
-/

-- Recursive type constructors
inductive tree (α : Type) : Type
| leaf : α               → tree
| node : tree → α → tree → tree

/-
Alternatively:
`inductive tree (α : Type) : Type`
`| leaf (x : α)                       : tree`
`| node (l : tree) (x : α) (r : tree) : tree`
(i.e. the syntax to abbreviate function parameters can be used on constructors)
-/

-- Make some terms of the above types...
section
  open maybe
  open tree
  
  #check maybe
  #check maybe ℕ
  #check nothing
  #check @nothing ℕ
  #check just 1
  
  #check tree
  #check tree int
  #check leaf 10
  #check @leaf int 10
  #check leaf (10 : int)
  #check (node (node (leaf 1) 2 (leaf 3)) 4 (node (leaf 5) 6 (leaf 7)) : tree int)
end

section
  #check tree          -- `Γ ⊢ (tree : Type → Type)`
  #check (Type → Type) -- `Γ ⊢ (Type → Type : Type 1)`
  -- variable x : tree (type error: a type constructor itself is not a well-formed type!)
end

-- In Lean, the naturals are defined as an inductive type:
inductive mynat : Type
| zero :         mynat
| succ : mynat → mynat

-- Make some terms of the above type...
section
  open mynat
  #check zero
  #check succ (succ (zero))
  #check zero.succ.succ.succ.succ -- Syntax for abbreviating
end

-- See: https://leanprover.github.io/reference/declarations.html#inductive-types
-- In general, the "inductive-formation" rule is used by the `inductive` keyword:
/-
`inductive <type-name> [parameters i.e. additional hypotheses...] : Sort <level>`
`| <constructor-name-1> : Π(...), ..., Π(...), <type-name>`
`| <constructor-name-2> : Π(...), ..., Π(...), <type-name>`
`| ...`
`| <constructor-name-n> : Π(...), ..., Π(...), <type-name>`

Each "constructor" is like a function that takes *zero or more arguments* and *return a term of type `<type-name>`*.
When specifying a constructor, the current type being declared (`<type-name>`) could be used in its type signature --
this makes the type "recursive".

The "inductive-introduction" rule is just a straightforward application of one of the constructors!
This is also *the only way* to make a term of that type "out of nothing"...
-/


--------------------------------------------------------------------------------
/-
If we are given a term of some inductive type, *we could be assured that it was built using one of the constructors.*
So if "*in all cases*, we could build another term (from the things 'went into' a constructor)", then we could indeed
build that term. This is called the "inductive-elimination" rule.
-/

-- **Inductive-elimination**

-- This special "method" `rec` is generated for each inductive type:
#check weekday.rec
#check maybe_int.rec
-- It is called a "recursor" or "eliminator". It takes one function as argument for each constructor of that
-- inductive type.
-- Each function is supposed to *take all arguments of the corresponding constructor* and *build a new term*.
-- Then it returns a function that "takes a term of that inductive type, and returns a new term".
#check @weekday.rec
#check @maybe_int.rec
-- (If you want more fine-grained control over the types of the new terms, put `@` in front of it and explicitly supply
--  a "typing function" aka. "motive" that gives the expected type of the new term for all cases.)
-- (This "typing function" is usually a constant function, but it can be defined using a recursor, too!
--  In that case the new term will be dependently typed.)

-- Let's make some functions using `rec` and give them names...
def number_of_day :=
  @weekday.rec (λ x, ℕ) 1 2 3 4 5 6 7

#check number_of_day
#reduce number_of_day weekday.sunday
#reduce number_of_day weekday.monday
#reduce number_of_day weekday.tuesday

def maybe_int_plus_one :=
  @maybe_int.rec (λ x, maybe_int)
    maybe_int.nothing             -- The "nothing" case.
    (λ x, maybe_int.just (x + 1)) -- The "just" case.

#check maybe_int_plus_one
#reduce maybe_int_plus_one (maybe_int.nothing)
#reduce maybe_int_plus_one (maybe_int.just 3)

-- For a type constructor, its `rec` method will take additional arguments... (note the `α` here)
def maybe_id {α : Type} :=
  @maybe.rec α (λ x, maybe α)
    (@maybe.nothing α)     -- The "nothing" case.
    (λ x, @maybe.just α x) -- The "just" case.

#reduce maybe_id (maybe.nothing)
#reduce maybe_id (maybe.just 1)

-- The "method" `rec_on` is a variant of `rec` that takes arguments in a different order.
/-
@weekday.rec :
  Π {motive : weekday → Sort u_1},
    motive weekday.sunday →
    motive weekday.monday →
    motive weekday.tuesday →
    motive weekday.wednesday →
    motive weekday.thursday →
    motive weekday.friday →
    motive weekday.saturday →
      Π (n : weekday), motive n

@weekday.rec_on :
  Π {motive : weekday → Sort u_1} (n : weekday),
    motive weekday.sunday →
    motive weekday.monday →
    motive weekday.tuesday →
    motive weekday.wednesday →
    motive weekday.thursday →
    motive weekday.friday →
    motive weekday.saturday →
      motive n
-/

-- Same function written using `rec_on`...
def number_of_day_1 (d : weekday) : ℕ :=
  weekday.rec_on d 1 2 3 4 5 6 7

#check number_of_day_1
#reduce number_of_day_1 weekday.sunday
#reduce number_of_day_1 weekday.monday
#reduce number_of_day_1 weekday.tuesday

-- (TODO: rephrase this paragraph...)
-- When defining a function that takes a term *of a recursive type* as argument, we have more information when building
-- a new term:
-- Look at the two `tree_int`s that went into the second constructor of `tree_int`. We could have made two recursive
-- function calls on them, and have received two new terms generated by these calls!
-- The recursor will provide these terms as additional arguments:

def tree_int_sum : tree_int → int :=
  @tree_int.rec
    (λ x, int)                              -- Typing function
    (λ x, x)                                -- The `leaf` case.
    (λ l x r, λ lsum rsum, lsum + x + rsum) -- The `node` case. Note the additional arguments `lsum` and `rsum`!

section
  open tree_int
  #reduce tree_int_sum (leaf 10)
  #reduce tree_int_sum (node (node (leaf 1) 2 (leaf 3)) 4 (leaf 5))
end

-- (i.e. now we can define functions recursively on inductive types!)
-- (This is called "definition by structural recursion"...)

def mynat_add : mynat → mynat → mynat :=
  λ x, @mynat.rec
    (λ r, mynat)         -- Typing function
    x                    -- The `zero` case (`x + 0` should be `x`)
    (λ r, λ xr, xr.succ) -- The `succ` case (`x + succ r` should be `succ (x + r)`)

-- See: https://leanprover.github.io/reference/declarations.html#inductive-types
-- In general, the "inductive-elimination" rule is used by the `rec` method:
/-
`@<type-name>.rec [parameters i.e. additional hypotheses...]`
`  (λ(x : <type-name...>), <type-for-the-new-term-constructed-from-x>)` -- (the "motive" or "typing function")
`  (λ(...), ..., λ(...), <new-term-for-constructor-1>)`
`  (λ(...), ..., λ(...), <new-term-for-constructor-2>)`
`  ...`
`  (λ(...), ..., λ(...), <new-term-for-constructor-n>)`
`  <term-of-the-inductive-type>`

Where the `λ(...), ..., λ(...)` accepts the same arguments from the corresponding constructor,
plus the new terms produced by "recursive calls" (if the corresponding constructor is recursive).

Special case: if the inductive type lives in `Prop`, the `λ(x : <type-name...>)` part in the motive
will vanish, and the motive could only return a `Prop`!
-/


--------------------------------------------------------------------------------
-- **Examples of inductive types**

-- TODO: logical connectives, quantifiers, natural numbers...
-- Go back and check the intelim rules for Σ, ×, +, 0, 1!

namespace hidden

inductive empty : Type

inductive unit : Type
| star : unit

inductive bool : Type
| ff : bool
| tt : bool

def ex_falso (α : Type) : empty → α := empty.rec (λx, α)

universes v

-- Type constructors
inductive prod (α : Type u) (β : Type v) : Type max u v
| mk : α → β → prod

variables α β : Type
variables (a : α) (b : β)

#check prod
#check @prod.mk
#check prod α β
#check prod.mk a b
#check @prod.rec.{1}

def fst {α : Type u} {β : Type v} (p : prod α β) : α :=
  prod.rec_on p (λ a b, a)

def snd {α : Type u} {β : Type v} (p : prod α β) : β :=
  prod.rec_on p (λ a b, b)

inductive sum (α : Type u) (β : Type v) : Type max u v
| inl : α → sum
| inr : β → sum

#check @sum.inl
#check @sum.inr
#check @sum.rec.{1}


inductive sigma {α : Type u} (β : α → Type v) : Type max u v
| dpair : Π a : α, β a → sigma

inductive option (α : Type u) : Type u
| none {} : option
| some    : α → option

inductive inhabited (α : Type u) : Type u
| mk : α → inhabited

def compose {α β γ : Type*} (f : β → option γ) (g : α → option β) (x : α) : option γ :=
  option.cases_on (g x) option.none f

-- set_option pp.all true

def is_even (x : ℕ) : bool := nat.rec_on x bool.tt (λ _, @bool.rec (λ _, bool) bool.tt bool.ff)

def filter (x : ℕ) : option ℕ := bool.cases_on (is_even x) (option.some x.succ) option.none

#reduce (compose filter filter) 0


-- TODO: how are the allowed universe levels determined for `inductive`...?
-- See: https://leanprover.github.io/theorem_proving_in_lean/inductive_types.html#axiomatic-details
inductive mysubtype {α : Sort u} (p : α → Prop) : Sort u
| mk : Π (x : α), Π (h : p x), mysubtype

#check @sigma   -- `Π {α : Type u_1}, (α → Type u_2) → Type (max u_1 u_2)`
#check @subtype -- `Π {α : Sort u_1}, (α → Prop) → Sort (max 1 u_1)`
#check @Exists  -- `Π {α : Sort u_1}, (α → Prop) → Prop`
-- "Subtype is inhabited -- the element satisfying the predicate is found -- the existential statement has a proof"

def add : ℕ → ℕ → ℕ := λ (n : ℕ), @nat.rec (λ _, ℕ) (n) (λ m add', add'.succ)
#reduce add 12 22



end hidden

namespace structures
-- `structure`s are special cases of inductive types!
-- They have only one constructor.

structure point (α : Type*) :=
  mk :: (x : α) (y : α) (z : α)

inductive color
| red
| green
| blue

structure color_point (α : Type*) extends point α :=
  mk :: (c : color)

structure rgb_val :=
  (red : nat)
  (green : nat)
  (blue : nat)

structure red_green_point (α : Type*) extends point α, rgb_val :=
  (no_blue : blue = 0)

def p   : point nat := { x := 10, y := 10, z := 20 }
def rgp : red_green_point nat :=
  { red := 200, green := 40, blue := 0, no_blue := rfl, ..p }

example : rgp.x   = 10  := rfl
example : rgp.red = 200 := rfl



end structures
end inductive_types


section inductive_families

--------------------------------------------------------------------------------
/-
There is an extension to inductive types... It's called "inductive families"!

"In fact, a single inductive definition can introduce an *indexed family* of inductive types,
 in a manner we now describe."

(Much like GADTs in Haskell!)
-/

-- Extended **inductive-formation** and **inductive-introduction**

-- Example: vector with length n
inductive vector (α : Type) : ℕ → Type
| nil  :                                   vector nat.zero
| cons : Π {n : ℕ} (a : α) (v : vector n), vector (nat.succ n)
-- (We may regard `vector` as a family of `Type`s "indexed" by an `ℕ`...
--  The rules for inductive families allow a constructor to return *one of them*.)

#check vector
#check vector ℕ 3
section
  open vector
  #check nil
  #check @nil ℕ
  #check cons
  #check @cons ℕ
  #check cons 3 (cons 2 (cons 1 nil))
end

/-
Note: in the example, `inductive vector (α : Type) : ℕ → Type` is NOT interchangeable with
  `inductive vector (α : Type) (n : ℕ) : Type` or `inductive vector : Type → ℕ → Type`!!
Lean treats indices of the family differently from parameters of the type former...

* Parameterised type (type former): this is achieved by "temporarily adding some hypotheses
  to the local context" and then "pop" these hypotheses while retaining the definitions...?
* Inductive family: this is another extension to the MLTT...? Different instance types
  can be "heterogeneous" and can be constructed from each other.

(TODO: make clear)
-/

-- Example: arithmetic expression
-- (cf. https://discord.com/channels/679792285910827018/679792285910827027/914149048016048148)
inductive Expr : Type → Type 1
| I   : ℤ                             → Expr ℤ
| B   : bool                          → Expr bool
| Id  : Π {α : Type}, Expr α          → Expr α
| Add : Expr ℤ → Expr ℤ               → Expr ℤ
| Mul : Expr ℤ → Expr ℤ               → Expr ℤ
| Eq  : Π {α : Type}, Expr α → Expr α → Expr bool

section
  open Expr
  -- Typechecks:
  #check Eq (B tt) (Eq (Add (I 10) (I 10)) (I (20)))
  -- Does not typecheck:
  -- #check Eq (Mul (I 1) (I 2)) (Eq (Add (I 10) (I 10)) (I (20)))
end

-- Example: equality (symmetric version)
-- https://xenaproject.wordpress.com/2021/04/18/induction-on-equality/
inductive myeq {α : Sort u} : α → α → Prop
| refl : Π (a : α), myeq a a

#check @myeq
#check @myeq ℕ 2 3
section
  open myeq
  #check myeq.refl
  #check @myeq.refl -- `∀ {α : Sort u} (a : α), myeq a a`
  #check ∀ {α : Sort u} (a : α), myeq a a -- `Prop`
  #check @myeq.refl ℕ 3 -- `myeq 3 3`
end

-- Example: equality (standard version)
inductive myeq' {α : Sort u} (a : α) : α → Prop
| refl [] : myeq' a -- `[]` makes the arguments explicit? TODO: which one?

#check @myeq'
#check @myeq' ℕ 2 3
section
  open myeq'
  #check myeq'.refl
  #check @myeq'.refl -- `∀ {α : Sort u} (a : α), myeq' a a`
  #check ∀ {α : Sort u} (a : α), myeq' a a -- `Prop`
  #check @myeq'.refl ℕ 3 -- `myeq' 3 3`
end

-- See: https://leanprover.github.io/reference/declarations.html#inductive-families
-- In general, the "inductive-formation" rule is used by the `inductive` keyword:
/-
`inductive <family-name> [parameters...] : Π(...), ..., Π (...), Sort <level>`
`| <constructor-name-1> : Π(...), ..., Π(...), <family-name> [indices]`
`| <constructor-name-2> : Π(...), ..., Π(...), <family-name> [indices]`
`| ...`
`| <constructor-name-n> : Π(...), ..., Π(...), <family-name> [indices]`

Each "constructor" is like a function that takes *zero or more arguments* and *return a term of type `<family-name> [indices]`*.
When specifying a constructor, the current family being declared (`<family-name>`) could be used in its type signature --
this makes the family "recursive".

The "inductive-introduction" rule is just a straightforward application of one of the constructors!
This is also *the only way* to make a term of any type in the family "out of nothing"...
-/


--------------------------------------------------------------------------------
/-
If we are given a term of some inductive family, *we could be assured that it was built using one of the constructors.*
So if "*in all cases*, we could build another term (from the things 'went into' a constructor)", then we could indeed
build that term. This is called the "inductive-elimination" rule.
-/

-- Extended **inductive-elimination**

-- This special "method" `rec` is generated for each inductive family:
#check @vector.rec
/-
@vector.rec :
  Π {α : Type}
    {motive : Π (n : ℕ), vector α n → Sort u},
                                                      motive 0 vector.nil →
    (Π {n : ℕ} (a : α) (v : vector α n), motive n v → motive n.succ (vector.cons a v)) →
      Π {n : ℕ} (v : vector α n), motive n v
-/

#check @Expr.rec
/-
@Expr.rec :
  Π {motive : Π (α : Type), Expr α → Sort u},
    (Π (x : ℤ),                                             motive ℤ (Expr.I x)) →
    (Π (x : bool),                                          motive bool (Expr.B x)) →
    (Π {α : Type} (x : Expr α),   motive α x →              motive α (Id x)) →
    (Π (x y : Expr ℤ),            motive ℤ x → motive ℤ y → motive ℤ (Add x y)) →
    (Π (x y : Expr ℤ),            motive ℤ x → motive ℤ y → motive ℤ (Mul x y)) →
    (Π {α : Type} (x y : Expr α), motive α x → motive α y → motive bool (Eq x y)) →
      Π {α : Type} (x : Expr α), motive α x
-/

#check @myeq.rec
/-
*Had this inductive family landed in universes other than `Prop`:*
@myeq.rec :
  Π {α : Sort u}                               -- Parameter
    {motive : Π (a b : α), myeq a b → Sort v}, -- Typing function
    (Π (a : α), motive a a (myeq.refl a)) →    -- `refl` (the only case)
      Π (a b : α) (h : myeq a b), motive a b h -- Resulting function
*But in reality:*
@myeq.rec :
  Π {α : Sort u}
    {motive : α → α → Sort v},                 -- *Something has vanished!*
    (Π (a : α), motive a a) →                  -- Since something has vanished, other things are going to vanish...
      Π (a b : α), myeq a b → motive a b       -- ...
-/

#check @myeq'.rec
/-
*Had this inductive family landed in universes other than `Prop`:*
@myeq'.rec :
  Π {α : Sort u} {a : α}                       -- Parameters
    {motive : Π (b : α), myeq' a b → Sort v},  -- Typing function
    (motive a (myeq'.refl a)) →                -- `refl` (the only case, nothing got fed into this constructor)
      Π (b : α) (h : myeq' a b), motive b h    -- Resulting function
*But in reality:*
@myeq'.rec :
  Π {α : Sort u} {a : α}
    {motive : α → Sort v},                     -- *Something has vanished!*
    (motive a) →                               -- Since something has vanished, other things are going to vanish...
      Π (b : α), myeq' a b → motive b          -- ...
-/

-- Let's make some functions using `rec` and give them names...

-- Sum of squares of all components
def vec_norm2 : Π {n : ℕ}, vector ℕ n → ℕ :=
  @vector.rec ℕ                         -- Parameter
    (λ n, λ (x : vector ℕ n), ℕ)        -- Typing function
    0                                   -- `nil`
    (λ n a v, λ norm2', norm2' + a * a) -- `cons`

#reduce vec_norm2 vector.nil
#reduce vec_norm2 (vector.cons 3 (vector.cons 2 (vector.cons 1 vector.nil)))

-- Evaluates an expression
def Expr_eval : Π {α : Type}, Expr α → α :=
  @Expr.rec
    (λ α, λ (x : Expr α), α)                             -- Typing function
    (λ (x : ℤ), x)                                       -- `I`
    (λ (x : bool), x)                                    -- `B`
    (λ (α : Type) (x : Expr α), λ (xval : α), xval)      -- `Id`
    (λ (x y : Expr ℤ), λ (xval yval : ℤ), xval + yval)   -- `Add`
    (λ (x y : Expr ℤ), λ (xval yval : ℤ), xval * yval)   -- `Mul`
    (λ (α : Type) (x y : Expr α), λ (xval yval : α), ff) -- `Eq` (TODO: add decidable_eq?)

section
  open Expr
  #reduce Expr_eval (Mul (Add (I 10) (I 10)) (I 2)) -- `40`
end

-- Theorems for equality are somewhat counterintuitive, in a similar way as how "ex falso quodlibet" is expressed in Lean...
-- Specifically, *a proof of the trivial case (refl) seems to be generalising over "non-existent" cases...*
-- We will start from the symmetric definition, then do the proofs again in the standard definition.

-- Theorems for the symmetric version
/-
"We have an element `h` of the type `myeq x y`. We are 100% sure that it was constructed
using `myeq.refl a` for some `a` (which generates a term of type `myeq a a`)!
So in order to make a proof of the goal `myeq (tmpl l) (tmpl r)` for every `myeq l r`,
we only need to make a proof of the goal `myeq (tmpl a) (tmpl a)` for any given `myeq a a`..."
-/
def myeq_congr : Π {α β : Sort u} (tmpl : α → β) (x y : α) (h : myeq x y), myeq (tmpl x) (tmpl y) :=
  λ α β tmpl x y h, @myeq.rec α     -- The subject is `myeq {α}`
    (λ l r, myeq (tmpl l) (tmpl r)) -- Make a more general claim: given `myeq l r` (vanished) then `myeq (tmpl l) (tmpl r)` 
    (λ a, myeq.refl (tmpl a))       -- Now given `myeq a a` (implicit), prove `myeq (tmpl a) (tmpl a)`
      x y h                         -- Then we could specialise `l` `r` to `x` `y`, and give a `myeq x y` to make a `myeq (tmpl x) (tmpl y)`

def myeq_symm : Π {α : Sort u} {x y : α} (h : myeq x y), myeq y x :=
  λ α x y h, @myeq.rec α            -- The subject is `myeq {α}`
    (λ l r, myeq r l)               -- Make a more general claim: given `myeq l r` (vanished) then `myeq r l`
    (λ a, myeq.refl a)              -- Now given `myeq a a` (implicit), prove `myeq a a`
      x y h                         -- Then we could specialise `l` `r` to `x` `y`, and give a `myeq x y` to make a `myeq y x`

def myeq_trans : Π {α : Sort u} {x y z : α} (h₁ : myeq x y) (h₂ : myeq y z), myeq x z :=
  λ α x y z h₁ h₂, @myeq.rec α      -- The subject is `myeq {α}`
    (λ l r, myeq x l → myeq x r)    -- Make a more general claim: given `myeq l r` (vanished) then `myeq x l → myeq x r`
    (λ a, id)                       -- Now given `myeq a a` (implicit), prove `myeq x a → myeq x a`
      y z h₂ h₁                     -- Then we could specialise `l` `r` to `y` `z`, and give a `myeq y z` to...

-- (The "implicit" means that you could construct an instance from the given `a` and the constructor `refl`,
--  so there is no point in giving you an instance in addition to `a`...)

section
  variables x y : ℕ
  #check myeq_congr (λ a : ℕ, 2 * a + 10) (x * 10) (y + 6)
  variables (h₁ : myeq 10 20) (h₂ : myeq 20 30)
  #check myeq_symm h₁
  #check myeq_trans h₁ h₂
end

-- Theorems for the standard version
def myeq'_congr : Π {α β : Sort u} (tmpl : α → β) (x y : α) (h : myeq' x y), myeq' (tmpl x) (tmpl y) :=
  λ α β tmpl x y h, @myeq'.rec α x  -- The subject is `myeq' {α} x`
    (λ r, myeq' (tmpl x) (tmpl r))  -- Make a more general claim: given `myeq' x r` (vanished) then `myeq' (tmpl x) (tmpl r)`
    (myeq'.refl (tmpl x))           -- Now given `myeq' x x` (implicit), prove `myeq' (tmpl x) (tmpl x)`
      y h                           -- Then we could specialise `r` to `y`, and give a `myeq x y` to make a `myeq (tmpl x) (tmpl y)`

def myeq'_symm : Π {α : Sort u} {x y : α} (h : myeq' x y), myeq' y x :=
  λ α x, @myeq'.rec α x             -- The subject is `myeq' {α} x`
    (λ r, myeq' r x)                -- Make a more general claim: given `myeq' x r` (vanished) then `myeq' r x`
    (myeq'.refl x)                  -- Now given a `myeq' x x` (implicit), prove `myeq' x x`
                                    -- Then we could specialise... and eta-reduce!

def myeq'_trans : Π {α : Sort u} {x y z : α} (h₁ : myeq' x y) (h₂ : myeq' y z), myeq' x z :=
  λ α x y z h₁ h₂, @myeq'.rec α x   -- The subject is `myeq' {α} x`
    (λ r, myeq' r z → myeq' x z)    -- Make a more general claim: given `myeq' x r` (vanished) then `myeq' r z → myeq' x z`
    id                              -- Now given a `myeq' x x` (implicit), prove `myeq' x z → myeq' x z`
      y h₁ h₂                       -- Then we could specialise `r` to `y`, and give a `myeq' x y` to make...

-- (The "implicit" means that you could construct an instance from the parameter `x` and the constructor `refl`,
--  so there is no point in giving you anything...)

section
  variables x y : ℕ
  #check myeq'_congr (λ a : ℕ, 2 * a + 10) (x * 10) (y + 6)
  variables (h₁ : myeq' 10 20) (h₂ : myeq' 20 30)
  #check myeq'_symm h₁
  #check myeq'_trans h₁ h₂
end

-- TODO: get used to it! (Induction to produce `Prop`, and "constructions generalising over non-existent cases"...)

-- See: https://leanprover.github.io/reference/declarations.html#inductive-families
-- TODO: make clear about the constraints
-- In general, the "inductive-elimination" rule is used by the `rec` method:
/-
`@<family-name>.rec [parameters...]`
`  (λ[indices], λ(x : <family-name...> [indices]), <type-for-the-new-term-constructed-from-x>)` -- (the "motive" or "typing function")
`  (λ(...), ..., λ(...), <new-term-for-constructor-1>)`
`  (λ(...), ..., λ(...), <new-term-for-constructor-2>)`
`  ...`
`  (λ(...), ..., λ(...), <new-term-for-constructor-n>)`
`  <term-of-the-inductive-type>`

Where the `λ(...), ..., λ(...)` accepts the same arguments from the corresponding constructor,
plus the new terms produced by "recursive calls" (if the corresponding constructor is recursive).

Special case: if the inductive type lives in `Prop`, the `λ(x : <family-name...> [indices])` part in the motive
will vanish (proof irrelevance?), and the motive could only return a `Prop`!

(Special case in special case: singleton elimination, as in our `myeq`s...)
-/


end inductive_families

--------------------------------------------------------------------------------

-- TODO: equality and computation rules

section judgmental_equality

/-
In type theory, we would like to ensure that every expression **has a unique type**.
However, it turns out that according to the rules above, an expression could have more than
one expressions assigned as its type, e.g.:

[WRONG; DELETE]
-/

parameter α : Type 1
parameter β : α → Type 1
parameter a : α

#check (sorry : α)

end judgmental_equality


--------------------------------------------------------------------------------

-- How could `#eval` calculate this so quickly?
#eval 12345 * 54321

-- TODO: `let` vs `λ`:
def foo := (let a := nat in λ x : a, x + 2)
-- def bar := (λ α, λ x : α, x + 2) nat -- Does not typecheck

-- TODO: check screenshots

-- TODO: review


--------------------------------------------------------------------------------
-- **The `Prop` universe**

/-
By virtue of the Curry-Howard correspondence, propositions can be represented as types.
The universe inhabited by all proposition types is called `Prop` in Lean.

Inside this universe, there are predefined types `true` and `false`.
Also there are some "type constructors" (i.e. functions that take types as input and produce types):

* `(∧) : Prop → Prop → Prop`
* `(∨) : Prop → Prop → Prop`
* `(→) : Sort u_1 → Sort u_2 → Sort (imax u_1 u_2)` (`Prop → Prop → Prop` is a special case)
* `(↔) : Prop → Prop → Prop`
* `not : Prop → Prop`

The last two constructors are dependently typed:

* `∀` is a literal synonym for `Π`                (primitive notion)
* `Exists : Π {α : Sort u_1}, (α → Prop) → Prop`  (not a primitive notion)
-/

#check true
#check true.intro
#check false
#check @false.elim

#check (∧)
#check (∨)
#check (→)
#check (↔)
#check not

-- ∀ is Π
-- Usage: `∀ (x : ℕ), x = x`
--   this is equvalent to `Π (x : ℕ), x = x`, which is the type of a function that produces
--   a term of type `x = x` upon being given any element `x` of type `ℕ`.
#check @Exists.{1}
-- Usage: `@Exists ℕ (λ (x : ℕ), x = x)`
--   where `ℕ` and `a = a` are types of the first element `a` and the second element in a
--   Σ (dependent pair), respectively.

/-
For the introduction / elimination rules for these types, see:

* https://leanprover.github.io/logic_and_proof/
* https://leanprover.github.io/theorem_proving_in_lean/propositions_and_proofs.html
* https://leanprover.github.io/theorem_proving_in_lean/quantifiers_and_equality.html

The `Prop` universe is specially treated when determining the "universe level" for a Π type.
Namely, in the Π-introduction rule, suppose we have `Γ ⊢ (α : Sort i)` and `Γ, (x : α) ⊢ (β a : Sort j)`,
Then `Γ ⊢ (Π (x : α), β x : Sort (imax i j))`, where `imax i j` is `0` if `j = 0`, and `max i j` otherwise.
In this way, if `β` is a proposition depending on `x`, then `Π (x : α), β x` is again a proposition.

The original purpose of "universe levels" is to avoid self-referential quantifications, i.e.

TODO: #####

"In particular, we can define predicates on α by quantifying over all predicates on α...???"

-/


section equation_compiler

--------------------------------------------------------------------------------
/-
Now we have largely explored Lean's type theory (and MLTT, and how MLTT is represented in Lean),
Let's try some additional functionalities provided by Lean's elaborator...
-/

-- **Recursion syntax and the Equation Compiler**




end equation_compiler

--------------------------------------------------------------------------------

/-
### Interacting with Lean

[](https://leanprover.github.io/theorem_proving_in_lean/interacting_with_lean.html)

* Importing files
* Sections
* Namespaces
* Attributes
* Implicit arguments
* Notations [TODO: complete]
* Coercions
* Displaying information
* Setting options
* Elaboration hints
* Using the library
-/

-- Automatic inserting of `coe`:

variables m n : ℕ
variables i j : ℤ

#check i + m      -- i + ↑m : ℤ
#check i + m + j  -- i + ↑m + j : ℤ
#check i + m + n  -- i + ↑m + ↑n : ℤ

#print notation ↑
#print notation ⇑
#print notation ↥

#check @coe_fn
#print has_coe_to_fun

#print nat

#check @prod.mk
#check @prod.fst
#check @prod.snd
#check @prod.rec


--------------------------------------------------------------------------------
-- Typeclasses

namespace hidden_typeclasses

class inhabited (α : Type _) :=
  mk :: (default : α)

instance Prop_inhabited : inhabited Prop :=
  inhabited.mk true

instance bool_inhabited : inhabited bool :=
  inhabited.mk tt

instance nat_inhabited : inhabited nat :=
  inhabited.mk 0

instance unit_inhabited : inhabited unit :=
  inhabited.mk ()

def default (α : Type*) [s : inhabited α] : α :=
  @inhabited.default α s

#reduce default Prop
#reduce default bool
#reduce default nat
#reduce default unit



end hidden_typeclasses

--------------------------------------------------------------------------------

namespace subtypes

inductive my_subtype {α : Type u} (p : α → Prop) : Type u
| mk : Π x : α, p x → my_subtype

section
  variables {α : Type u} (p : α → Prop)
  
  #check @my_subtype
  #check (α → Prop) → Type u
  #check Π {α : Type u}, (α → Prop) → Type u

  #check my_subtype p
  #check {x : α // p x}
end

end subtypes

#check (eq ℕ)

#check @ite

inductive mylist (α : Type*)
| nil {} : mylist
| cons   : α → mylist → mylist

#check mylist.nil

/-
inductive my_and (α : Type) (β : Type) : Type
| intro : Type → Type → my_and

#check my_and.intro true true
-/

#check and true true

#check and
#check eq ℕ
#check Type → Prop
#check Π (x : Prop) (y : Prop), Prop
#check Π (α : Type) (a : α), Prop

