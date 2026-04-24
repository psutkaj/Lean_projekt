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

theorem hard : FermatLastTheorem := by
  sorry

#check hard

example
  (x y : ℝ) (h : x < y) :
  x + 1 < y + 1 := by
  simp
  exact h


theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  · exact hp
  constructor
  · exact hq
  · exact hp

example
  (P Q R S: Prop) (hSQ : S = Q)
  (hR : R) (hRQ : R → Q) :
  P → S :=
by
  intro hP
  rw [hSQ]
  apply hRQ
  exact hR




example (P : Prop) (hP : P) : P := by
  exact hP


example
  (h : ∃ x : ℝ, x < 0) :
  ∃ u : ℝ, -u ≥ 0 := by
  obtain ⟨z, hz⟩ := h
  have z_nonneg : z ≤ 0 := by linarith
  use z
  simp
  exact z_nonneg


example
  (a b c : ℝ)
  (ha : a < b) (hb : b < c) :
  a < c := by
  linarith

example (a b : ℝ) :
  (a + b)^2 = a^2 + 2*a*b + b^2 := by
  calc (a + b)^2
  _ = (a + b) * (a + b) := pow_two (a + b)
  _ = a * (a + b) + b * (a + b) := RightDistribClass.right_distrib a b (a + b)
  _ = a * a + b * a + a * b + b * b := by group
  _ = a^2 + 2*a*b + b^2 := by group
