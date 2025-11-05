import LEANprj.Sequences.defs

-- zavedu jako axiom, z uplnosti Realnych cisel
axiom exists_point_in_nested_intervals
  (l u : ℕ → ℝ)
  (inc_l : IncreasingSequence l)
  (dec_u : DecreasingSequence u)
  (sep : ∀ n, l n ≤ u n)
  (shrink : ∀ n, u (n+1) - l (n+1) < (u n - l n)) :
  ∃ s : ℝ, ∀ n, l n ≤ s ∧ s ≤ u n

theorem nested_niqueness (l u : ℕ → ℝ)
  (inc_l : IncreasingSequence l)
  (dec_u : DecreasingSequence u)
  (sep : ∀ n, l n ≤ u n)
  (shrink : ∀ n, u (n+1) - l (n+1) < (u n - l n)) :
  ∃! s : ℝ, ∀ n : ℕ, l n ≤ s ∧ s ≤ u n := by
  obtain ⟨t, ht⟩ := exists_point_in_nested_intervals l u inc_l dec_u sep shrink
  sorry
