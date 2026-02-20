import LEANprj.defs

theorem Something {f : ℝ → ℝ} {hf : Continuous f} : Continuous f := by
  exact hf


def m : ℕ := 1

#check m

def FermatLastTheorem' :=
  ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

#check FermatLastTheorem'

theorem easy : 2 + 2 = 4 :=
  rfl

#check easy

theorem hard : FermatLastTheorem :=
  have a := 1
  have a := 2
  have a := 3
  have a := 4
  sorry

#check hard

example
  (x y : ℝ) (h : x < y) :
  x + 1 < y + 1 := by
  simp
  exact h
