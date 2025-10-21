import LEANprj.Sequences.definitions

example (a : ℕ → ℝ) (ha : ∀ n : ℕ, a n = (n / (n + 1))) : ConvergentTo a 1 := by
  unfold ConvergentTo
  intro ε ε_pos
  use (Int.ceil (1 / ε - 1)).toNat
  sorry
