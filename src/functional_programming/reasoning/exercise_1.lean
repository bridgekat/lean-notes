import data.nat.basic
import data.list.basic


@[simp]
def concat_pair {α β : Type} : list α × list β → list α × list β → list α × list β
| ⟨xs, ys⟩ ⟨xs', ys'⟩ := (xs ++ xs', ys ++ ys')

local infix ` <> ` : 65 := concat_pair

lemma A {α β : Type} (xs : list α × list β) : xs <> ([], []) = xs ∧ ([], []) <> xs = xs :=
  let ⟨xs₁, ys₂⟩ := xs in ⟨by simp, rfl⟩

lemma B {α β : Type} (xs ys zs : list α × list β) : (xs <> ys) <> zs = xs <> (ys <> zs) := by
  { rcases xs with ⟨xs₁, xs₂⟩,
    rcases ys with ⟨ys₁, ys₂⟩,
    rcases zs with ⟨zs₁, zs₂⟩,
    simp }

-- a)

def split {α β : Type} : list (α × β) → list α × list β
| []             := ([], [])
| ((x, y) :: zs) := ([x], [y]) <> (split zs)

#eval split [(1, 'a'), (2, 'b')]

-- b)

def splitTR {α β : Type} : list (α × β) → list α → list β → list α × list β
| []             xs ys := (xs, ys)
| ((x, y) :: zs) xs ys := splitTR zs (xs ++ [x]) (ys ++ [y])

#eval splitTR [(5, 'e'), (2, 'b')] [3, 6] ['c', 'f']

-- c)

lemma C {α β : Type} (zs : list (α × β)) (xs : list α) (ys : list β) :
  splitTR zs xs ys = (xs, ys) <> split zs := by
  { induction zs with hzs tzs ih generalizing xs ys,
    { unfold split, rw (A _).left, refl },
    { cases hzs with x y,
      unfold split, rw ← B,
      unfold splitTR, rw ih,
      refl } }

-- d)

lemma D {α β : Type} (zs : list (α × β)) :
  splitTR zs [] [] = split zs := by
  { suffices : splitTR zs [] [] = ([], []) <> split zs,
    { rw (A _).right at this, exact this },
    { exact C _ _ _ } }

