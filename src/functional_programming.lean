-- # Tony Field's unassessed Haskell exercises
-- Now in Lean!

import data.nat.basic
import data.nat.pow
import data.nat.sqrt


--------------------------------------------------------------------------------
-- ## Exercise 1 (Basics)

section exercise_1

-- **(1)**

-- Type inference (elaboration) precedes evaluation (reduction)!
-- (Coercions are usually inserted for "atomic" terms...?)
#eval 2 - 3 - 4
#eval (2 : int) - (3 : int) - (4 : int)
#eval ((2 - 3 - 4) : int)

-- `/` (integer division) is left-associative
#eval 100 / 4 / 5
#eval 100 / (4 / 5)

-- `^` is right-associative
#eval 2 ^ 3 ^ 2

#eval (3 - 5 * 4 : int)
#eval 2 ^ 2 * 3
#eval 2 * 2 ^ 3

-- Intuitionistic (propositional) equality does not return a `Bool`!
-- They produce a `Prop` instead.
#reduce ((3 + 4 - 5) : int) = ((3 - 5 + 4) : int)


-- Internally, `char`s are represented by a natural number denoting its Unicode,
-- along with a proof that the natural number falls in a valid Unicode range.
-- They can be accessed by `.val` and `.valid` respectively.
#reduce 'a'.val
#check 'a'.valid
-- We also say that `char` is a `subtype` of `nat`. (The type of the second
-- element is a predicate on `nat`, which is like declaring a specific subset
-- of `nat`.)

-- To convert naturals to chars, we need to prove this...
theorem h₁ : is_valid_char 97 :=
begin
  unfold is_valid_char,
  left,
  simp,
end
-- `char.mk` is the only constructor for `char`.
#eval char.mk ('b'.val - 1) h₁

theorem h₂ : is_valid_char 120 :=
begin
  left,
  simp,
end
-- Alternatively, we may use `⟨` `⟩` to represent this unique constructor.
#eval (⟨'X'.val + ('a'.val - 'A'.val), h₂⟩ : char)

/-
#eval char.mk ('X'.val + ('a'.val - 'A'.val))
begin
  -- Another option that completes the proof "in-line" (why so slow?)
  unfold is_valid_char,
  left,
  change 120 < 55296 at ⊢,
  simp,
end
-/

-- Not sure why this hangs...
-- #reduce ('p') ≠ ('p')
#reduce ('h') ≤ ('u')

-- Surely there are no floating point numbers in Lean!
#eval nat.sqrt (2 ^ 2 : ℕ)

-- But there are floating point numbers in Lean's metaprograms...
#eval native.float.sqrt (2 ^ 2)
#eval native.float.sqrt (2 ^ 2) - 2

-- **(2)**

#eval 123 % 10
#eval 456 / 100

theorem h₃ : is_valid_char 104 :=
begin
  left,
  simp,
end
#eval char.mk ('a'.val + 8 - 1) h₃

-- **(3)**

#reduce ¬(2 * 3 = 10)
#reduce (3 = 4) ↔ ⊤

def if_then_else {α : Type*} : bool → α → α → α
| tt := λ x y, x -- These constructs are also called "Church Booleans"
| ff := λ x y, y

#reduce (if_then_else tt 1 2) = 3
-- Could we convert the following into a `char`?
#reduce (if_then_else (3 = 4) 'a'.val 'b'.val + 1)
#reduce 8 > 2 ^ (if_then_else (3 = 4) 2 3) ↔ ⊥

-- **(4)**

#reduce (1, 2) < (1, 4)
#reduce ((4, 9), (3, 1)) > ((1, 10), (9, 4))
-- Not sure why the following hangs...
-- (Probably it is trying to expand the validity proofs in `char`s?)
-- #reduce ('a', 5, (3, 'b')) < ('a', 5, (3, 'c'))

-- **(5)**

-- "Tuples" are in fact nested pairs... (see output)
#eval let s : ℕ := 8473 in (s / 3600, s / 60 % 60, s % 60)
-- `let` expressions are much like "λ-abstractions" (although there are some
-- minor differences...)
#eval (λ s, (s / 3600, s / 60 % 60, s % 60)) 8473

-- **(6)**

section
  open native
  -- But with `let` you may also do "pattern matching"...
  #eval (let (r, θ) := (1, float.pi / 4)
         in (r * float.cos θ, r * float.sin θ) : float × float)
end

-- **(7)**

-- Seems like you need to explicitly specify types for some `let` expressions...
-- (TODO: why?)
#eval (let (x, y) := (3, 8) in (x, y, 24) : ℕ × ℕ × ℕ)
-- #eval (let (x, y) := (1, 2, 3) in (x - y) : ℕ) -- Type error
#eval (let (x, (y, b)) := (7, (6, tt)) in (if_then_else b (x - y) 0) : ℕ)

-- In the following expression, the type of `p` could be inferred when we
-- first encounter `p := (6, 5)`... If we use λ, this will be a type error!
#eval (let p := (6, 5) in (let ((a, b), c) := (p, '*') in (b, c) : ℕ × char))
#eval (let p := (tt, 1) in (tt, p))

-- **(8)**

def quotRem : ℕ → ℕ → (ℕ × ℕ) := λ n m, (n / m, n % m)
#eval (let (q, r) := quotRem 24 10 in (q * 10 + q) * 100 + r * 10 + r : ℕ)

-- **(9)**

-- TODO: do we have list comprehensions in Lean?

end exercise_1


--------------------------------------------------------------------------------
-- ### Exercise 2 (Functions)

section exercise_2



end exercise_2


