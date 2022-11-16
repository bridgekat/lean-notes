import tactic

---------------
-- # Question 1
---------------

namespace coursework.i

inductive loc : Type
| id    : ℕ → loc
| deref : ℕ → loc

inductive exp : Type
| loc    : loc →       exp
| int    : ℤ →         exp -- Normal (answer)
| dderef : ℕ →         exp
| sum    : exp → exp → exp
| prod   : exp → exp → exp

inductive cmd : Type
| skip   :             cmd -- Normal (answer)
| assign : loc → exp → cmd
| seq    : cmd → cmd → cmd
| cond   : loc → cmd → cmd → cmd
| while  : loc → cmd → cmd

-- Notations
instance : has_coe ℕ loc := ⟨loc.id⟩
notation `$`:100 n:100   := loc.deref n

instance name₁ : has_coe loc exp := ⟨exp.loc⟩
instance name₂ : has_coe ℤ exp   := ⟨exp.int⟩
notation `$$`:100 n:100          := exp.dderef n
instance : has_add exp           := ⟨exp.sum⟩
instance : has_mul exp           := ⟨exp.prod⟩

notation `SKIP`                                    := cmd.skip
infixr   ` ::= `:50                                := cmd.assign
infixr   ` ;; `:25                                 := cmd.seq
notation `IF ` c:100 ` THEN ` t:100 ` ELSE ` f:100 := cmd.cond c t f
notation `WHILE ` c:100 ` DO ` b:100               := cmd.while c b

-- Heap defined as a funtion from ℕ to (optional ℤ)
-- This may not be the best for proving theorems, but easily enables computation.
def heap : Type := ℕ → option ℤ
def heap.empty : heap := λ i', none
def heap.set : heap → ℕ → ℤ → heap
| h i x := λ i', if i' = i then x else h i'

def heap.from_list : list (ℕ × ℤ) → heap
| (list.nil)           := λ i', none
| (list.cons ⟨i, x⟩ t) := λ i', if i' = i then x else heap.from_list t i'

meta def heap.to_list : heap → ℕ → ℕ → list (option ℤ)
| h l r := if l = r then [] else list.cons (h l) (heap.to_list h (l + 1) r)

-- Big-step operational semantics (interpreter)
def loc.eval : loc → heap → option ℤ
| (loc.id i)    h := i
| (loc.deref i) h := h i

def exp.eval : exp → heap → option ℤ
| (exp.loc l)    h := loc.eval l h
| (exp.int z)    h := some z
| (exp.dderef i) h := do
  i' <- h i,
  match i' with
  | (int.of_nat i')         := h i'
  | (int.neg_succ_of_nat _) := none
  end
| (exp.sum a b)  h := do a' <- exp.eval a h, b' <- exp.eval b h, some (a' + b')
| (exp.prod a b) h := do a' <- exp.eval a h, b' <- exp.eval b h, some (a' * b')

meta def cmd.exec : cmd → heap → option heap
| (cmd.skip)       h := h
| (cmd.assign i x) h := do
  i' <- loc.eval i h,
  x' <- exp.eval x h,
  match i' with
  | (int.of_nat i')         := heap.set h i' x'
  | (int.neg_succ_of_nat _) := none
  end
| (cmd.seq c₁ c₂) h := do
  h₁ <- cmd.exec c₁ h,
  h₂ <- cmd.exec c₂ h₁,
  some h₂
| (cmd.cond c t f) h := do
  c' <- loc.eval c h,
  if c' > 0 then cmd.exec t h else cmd.exec f h
| (cmd.while c b) h := do
  c' <- loc.eval c h,
  if c' > 0 then cmd.exec (cmd.seq b (cmd.while c b)) h else cmd.exec cmd.skip h

-- Part A
section
  def prog₁ : cmd :=
    ↑1 ::= ↑0;;
    ↑2 ::= ↑1;;
    ↑3 ::= $0

  #eval do
    h <- cmd.exec prog₁ (heap.from_list [(0, 3)]),
    some (heap.to_list h 0 10)
  -- [(some 3), (some 0), (some 1), (some 3), none, none, none, none, none, none]

  def prog₂ : cmd :=
    ↑1 ::= ↑0;;
    ↑2 ::= ↑1;;
    ↑3 ::= $0;;
    WHILE $3 DO (
      ↑2 ::= $2 * $3;;
      ↑3 ::= $3 + ↑(-1:ℤ)
    );;
    ↑1 ::= $2

  #eval do
    h <- cmd.exec prog₂ (heap.from_list [(0, 3)]),
    some (heap.to_list h 0 10)
  -- [(some 3), (some 6), (some 6), (some 0), none, none, none, none, none, none]
end

-- Part B
-- The `loc.eval : loc → heap → option ℤ` is the "auxiliary lookup function for locations".
-- Note that Lean prefers coercions on smallest terms, e.g.
-- `z₁ + z₂` is interpreted as `(expr.int z₁) + (expr.int z₂)` instead of `expr.int (z₁ + z₂)`.
inductive exp_small : exp × heap → exp × heap → Prop
| loc        : ∀ (h : heap) (l : loc) (z : ℤ),    loc.eval l h = some z →         exp_small (l, h) (z, h)
| dderef     : ∀ (h : heap) (n n' : ℕ) (z : ℤ),   h n = some n' → h n' = some z → exp_small ($$n, h) (z, h)
| sum_left   : ∀ (h : heap) (E₁ E₁' E₂ : exp),    exp_small (E₁, h) (E₁', h) →    exp_small (E₁ + E₂, h) (E₁' + E₂, h)
| sum_right  : ∀ (h : heap) (z : ℤ) (E E' : exp), exp_small (E, h) (E', h) →      exp_small (z + E, h) (z + E', h)
| sum_add    : ∀ (h : heap) (z₁ z₂ z : ℤ),        z₁ + z₂ = z →                   exp_small (z₁ + z₂, h) (z, h)
| prod_left  : ∀ (h : heap) (E₁ E₁' E₂ : exp),    exp_small (E₁, h) (E₁', h) →    exp_small (E₁ * E₂, h) (E₁' * E₂, h)
| prod_right : ∀ (h : heap) (z : ℤ) (E E' : exp), exp_small (E, h) (E', h) →      exp_small (z * E, h) (z * E', h)
| prod_mul   : ∀ (h : heap) (z₁ z₂ z : ℤ),        z₁ + z₂ = z →                   exp_small (z₁ * z₂, h) (z, h)

-- Technically speaking, in this problem we cannot make a `cond_left` rule that evaluates the condition only,
-- as the type of the condition is Loc, which could only store a non-negative constant.
inductive cmd_small : cmd × heap → cmd × heap → Prop
| assign_left  : ∀ (h : heap) (l : loc) (n : ℕ) (E : exp),     loc.eval l h = some (int.of_nat n) → cmd_small (l ::= E, h) (n ::= E, h)
| assign_right : ∀ (h : heap) (n : ℕ) (E E' : exp),            exp_small (E, h) (E', h) →           cmd_small (n ::= E, h) (n ::= E', h)
| assign_set   : ∀ (h h' : heap) (n : ℕ) (z : ℤ),              heap.set h n z = h' →                cmd_small (n ::= z, h) (SKIP, h')
| seq_left     : ∀ (h h' : heap) (C₁ C₁' C₂: cmd),             cmd_small (C₁, h) (C₁', h') →        cmd_small (C₁ ;; C₂, h) (C₁' ;; C₂, h')
| seq_skip     : ∀ (h : heap) (C : cmd),                                                            cmd_small (SKIP ;; C, h) (C, h)
| cond_true    : ∀ (h : heap) (l : loc) (z : ℤ) (c₁ c₂ : cmd), loc.eval l h = some z → z > 0 →      cmd_small (IF l THEN c₁ ELSE c₂, h) (c₁, h)
| cond_false   : ∀ (h : heap) (l : loc) (z : ℤ) (c₁ c₂ : cmd), loc.eval l h = some z → z <= 0 →     cmd_small (IF l THEN c₁ ELSE c₂, h) (c₂, h)
| while        : ∀ (h : heap) (l : loc) (c : cmd),                                                  cmd_small (WHILE l DO c, h) (IF l THEN (c ;; WHILE l DO c) ELSE SKIP, h)

notation p₁ ` ~>ᵉ ` p₂ := exp_small p₁ p₂
notation p₁ ` ~>ᶜ ` p₂ := cmd_small p₁ p₂

-- Part C
/-
* Answer configurations: (`SKIP`, h)
* Stuck configurations: (C, h) where C contains any of the following:
  * an Loc `$n`, where `h` is not defined at index `n`;
  * an Exp `$$n`, where `h` is not defined at indices `n` or `$n` (including the case `$n` evaluates to a negative integer);
  * a Cmd `l ::= E`, where `l` (an Loc) evaluates to a negative integer.
* Normal configurations: all of the above.
-/

-- Part D
section
  def add5 : cmd :=
    ↑2 ::= $1;;
    -- Loop invariant: location 2 stores the current pointer
    WHILE $2 DO (
      $2 ::= $$2 + ↑5;;
      ↑2 ::= $2 + ↑1;;
      ↑2 ::= $$2
    )

  #eval do
    h <- cmd.exec add5 (heap.from_list [(1, 15), (12, -25), (13, 17), (15, 4), (16, 12), (17, 28), (18, -111)]),
    some (heap.to_list h 0 20)
  -- [none, (some 15), (some -111), none, none, none, none, none, none, none,
  --  none, none, (some -20), (some 17), none, (some 9), (some 12), (some 33), (some -111), none]
end

end coursework.i

---------------
-- # Question 2
---------------

namespace coursework.ii

inductive exp : Type
| num  : ℕ →         exp
| sum  : exp → exp → exp
| prod : exp → exp → exp

instance : has_coe ℕ exp := ⟨exp.num⟩
instance : has_add exp := ⟨exp.sum⟩
instance : has_mul exp := ⟨exp.prod⟩

inductive small : exp → exp → Prop
| sum1  : ∀ (n₁ n₂ m : ℕ),          n₁ + n₂ = m  → small (n₁ + n₂) m
| sum2  : ∀ (E₁ E₁' E₂ : exp),      small E₁ E₁' → small (E₁ + E₂) (E₁' + E₂)
| sum3  : ∀ (n : ℕ) (E₂ E₂' : exp), small E₂ E₂' → small (n + E₂) (n + E₂')
| prod1 : ∀ (E₁ E₁' E₂ : exp),      small E₁ E₁' → small (E₁ * E₂) (E₁' * E₂)
| prod2 : ∀ (n m : ℕ) (E₂ : exp),   n = m + 1 →    small (n * E₂) (E₂ + (m * E₂))
| prod3 : ∀ (E₂ : exp),                            small (↑0 * E₂) ↑0

notation E₁ ` ~> ` E₂ := small E₁ E₂

-- Part A
section
  variable R : exp → exp → Prop
  #check @small.rec R
  /-
  small.rec :
  (∀ (n₁ n₂ m : ℕ)           n₁ + n₂ = m →            R (↑n₁ + ↑n₂) ↑m          ) →
  (∀ (E₁ E₁' E₂ : exp),      (E₁ ~> E₁') → R E₁ E₁' → R (E₁ + E₂) (E₁' + E₂)    ) →
  (∀ (n : ℕ) (E₂ E₂' : exp), (E₂ ~> E₂') → R E₂ E₂' → R (↑n + E₂) (↑n + E₂')    ) →
  (∀ (E₁ E₁' E₂ : exp),      (E₁ ~> E₁') → R E₁ E₁' → R (E₁ * E₂) (E₁' * E₂)    ) →
  (∀ (n m : ℕ) (E₂ : exp),   n = m + 1 →              R (↑n * E₂) (E₂ + ↑m * E₂)) →
  (∀ (E₂ : exp),                                      R (↑0 * E₂) ↑0            ) →
  ∀ (E₁ E₂ : exp), (E₁ ~> E₂) → R E₁ E₂
  -/
end

-- Part B
def eval : exp → ℕ
| (exp.num n)      := n
| (exp.sum E₁ E₂)  := eval E₁ + eval E₂
| (exp.prod E₁ E₂) := eval E₁ * eval E₂

theorem part_b : ∀ E E' : exp, (E ~> E') → (eval E = eval E') :=
begin
  rintros E E' hs,
  induction hs,
  case sum1  : n₁ n₂ m hsum        { rw ← hsum, refl },
  case sum2  : E₁ E₁' E₂ hsmall ih { change eval E₁ + eval E₂ = eval E₁' + eval E₂ at ⊢, rw ih, },
  case sum3  : n E₂ E₂' hsmall ih  { change n + eval E₂ = n + eval E₂' at ⊢, rw ih, },
  case prod1 : E₁ E₁' E₂ hsmall ih { change eval E₁ * eval E₂ = eval E₁' * eval E₂ at ⊢, rw ih, },
  case prod2 : n m E₂ hsucc        { change n * eval E₂ = eval E₂ + m * eval E₂ at ⊢, rw hsucc, linarith, },
  case prod3 : E₂                  { change 0 * eval E₂ = 0 at ⊢, linarith, },
end

-- Part C
inductive small_star : exp → exp → Prop
| refl : ∀ (E : exp),                                        small_star E E
| tail : ∀ (E₁ E₂ E₃ : exp), small_star E₁ E₂ → (E₂ ~> E₃) → small_star E₁ E₃

notation E₁ ` ~>* ` E₂ := small_star E₁ E₂

section
  variable R : exp → exp → Prop
  #check @small_star.rec R
  /-
  small_star.rec :
  (∀ (E : exp),                                             R E E  ) →
  (∀ (E₁ E₂ E₃ : exp), (E₁ ~>* E₂) → (E₂ ~> E₃) → R E₁ E₂ → R E₁ E₃) →
  ∀ (E₁ E₂ : exp), (E₁ ~>* E₂) → R E₁ E₂
  -/
end

-- Part D
theorem part_d : ∀ E E' : exp, (E ~>* E') → eval E = eval E' :=
begin
  rintros E E' hss,
  induction hss,
  case refl : E { refl, },
  case tail : E₁ E₂ E₃ hss hs ih { rw ih, exact (part_b _ _ hs), },
end

-- Part E
theorem part_e : ∀ E : exp, ∀ n : ℕ, (E ~>* n) → eval E = n :=
begin
  rintros E n hss,
  exact (part_d _ _ hss),
end

end coursework.ii
