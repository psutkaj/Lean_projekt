import Mathlib

def ConvergesTo (a : ℕ → ℝ) (p : ℝ) := ∀ ε > 0, ∃ nₒ, ∀ n ≥ nₒ, |a n - p| < ε

theorem Uniqueness
  (a : ℕ → ℝ) (p q : ℝ) (h₁ : ConvergesTo a p) (h₂ : ConvergesTo a q) : p = q :=
by
  by_contra hne
  have hab : |p - q| > 0 := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hpos : 0 < |p - q| / 2 := half_pos hab
  rcases h₁ (|p - q| / 2) hpos with ⟨n₁,hn₁⟩
  rcases h₂ (|p - q| / 2) hpos with ⟨n₂,hn₂⟩
  let nₒ := max n₁ n₂
  have hn₁e : |a nₒ - p| < |p - q| / 2 := hn₁ nₒ (le_max_left  n₁ n₂)
  have hn₂e : |a nₒ - q| < |p - q| / 2 := hn₂ nₒ (le_max_right n₁ n₂)
  have : |p - q| < |p - q| := by
    calc
      |p - q| = |(p - a nₒ) + (a nₒ - q)| := by simp [sub_add_sub_cancel]
      _ ≤ |p - a nₒ| + |a nₒ - q| := abs_add _ _
      _ = |a nₒ - p| + |a nₒ - q| := by rw [abs_sub_comm p (a nₒ)]
      _ < |p - q| / 2 + |p - q| / 2 := add_lt_add hn₁e hn₂e
      _ = |p - q| := by ring
  linarith
