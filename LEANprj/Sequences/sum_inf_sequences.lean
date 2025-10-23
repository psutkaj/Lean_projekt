import LEANprj.Sequences.definitions

example (a : ℕ → ℝ) (ha : ∀ n : ℕ, a n = 1) : IsSup a 1 := by
  unfold IsSup
  intro x x_1
  constructor
  obtain ⟨n, hn⟩ := x_1
  rw [ha] at hn
  linarith
  intro ε ε_pos
  use 1
  constructor
  tauto
  linarith
