import LEANprj.Sequences.definitions

example (a : ℕ → ℝ) (ha: ∀ n : ℕ, a n = n) : StrictlyIncreasingSequence a := by
  unfold StrictlyIncreasingSequence
  intro n
  rw [ha, ha]
  norm_cast
  linarith

example (a : ℕ → ℝ) (ha: ∀ n : ℕ, a n = (n / (n + 1))) : StrictlyIncreasingSequence a := by
  unfold StrictlyIncreasingSequence
  intro n
  rw [ha, ha]
  norm_cast
  simp
  have h₁ : (↑n + 1) > 0 := by linarith
  have h₂ : (↑n + 1 + 1) > 0 := by linarith
  refine (div_lt_div_iff₀ ?_ ?_).mpr ?_
  linarith
  linarith
  nlinarith
