import data.real.basic
import init.meta.float
import tactic
import system.io
open io


structure vertex3 (α : Type*) := mk :: (x : α) (y : α) (z : α)

#check @vertex3.{0}
#check @vertex3.rec_on.{1}
#check @vertex3.x.{0}
#check @vertex3.y.{0}
#check @vertex3.z.{0}

#print prefix vertex3

#reduce vertex3.x (vertex3.mk 10 20 30)
#eval vertex3.y (vertex3.mk 10 20 30)
#eval vertex3.z (vertex3.mk 10 20 30)

def hello_world : io unit :=
  put_str_ln "Hello, world!" >>= λ _,
  put_str_ln "Hello world again!" >>= λ _,
  return unit.star

def hello_world_2 : io unit := do
  put_str_ln "Hello, world!",
  put_str_ln "Hello world again!"

#eval hello_world
#eval hello_world_2

#print axioms hello_world


namespace hidden

inductive tree (α : Type) : Type
| leaf : α               → tree
| node : tree → α → tree → tree

#check hidden.tree
open hidden.tree

def a_tree : tree ℕ := node (node (leaf 1) 2 (leaf 3)) 4 (node (leaf 5) 6 (leaf 7))

-- By recursor
def fmap {α β : Type} : (α → β) → tree α → tree β := λ f a,
  tree.rec (λ x, leaf (f x)) (λ l x r, λ l' r', node l' (f x) r') a

-- By pattern matching ("well-founded recursion" by "equation compiler")
def fmap' {α β : Type} : (α → β) → tree α → tree β
| f (leaf x)     := leaf (f x)
| f (node l x r) := node (fmap' f l) (f x) (fmap' f r)

#reduce fmap (λ x, x + 1) a_tree
#reduce fmap' (λ x, x + 1) a_tree

/-
class functor (γ : Type) :=
  fmap :: (α → β) → functor α → functor β
-/

end hidden

--------------------------------------------------------------------------------

meta def m91 : ℕ → ℕ
| n := if n > 100 then n - 10 else m91 (m91 (n + 11))

#eval m91 10
#eval m91 100
#eval m91 1000

meta def foo : ℕ → ℕ
| n := foo n + 1
-- #reduce foo
-- #eval foo 0


/-
prelude -- Disable all non-primitive notions

inductive mynat : Type
| zero :         mynat
| succ : mynat → mynat

#print prefix mynat
-/









