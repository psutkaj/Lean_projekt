import LEANprj.Sequences.definitions

example (a : ℕ → ℝ) (ha: ∀ n : ℕ, a n = n) : StrictlyIncreasingSequence a := by
  unfold StrictlyIncreasingSequence
  intro n
  rw [ha, ha]
  norm_cast
  linarith
