import LEANprj.Sequences.definitions

example (a : ℕ → ℝ)  (ha :∀ n : ℕ, a n = 1 ) : ConvergentTo a 1 := by
  unfold ConvergentTo
  intro ε ε_pos
  use 0
  intro n hn
  rw [ha]
  simp
  linarith

example (a : ℕ → ℝ) (ha : ∀ n : ℕ, a n = 1 / n) : ConvergentTo a 0 := by
  intros ε ε_pos
  use (Int.ceil (1/ε)).toNat
  intro n n_gt
  rw [ha]
