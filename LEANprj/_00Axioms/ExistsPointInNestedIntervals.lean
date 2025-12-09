import LEANprj.defs

axiom ExistsPointInNestedIntervals
  (l u : ℕ → ℝ)
  (inc_l : IncreasingSequence l)
  (dec_u : DecreasingSequence u)
  (sep : ∀ n, l n ≤ u n) :
  ∃ s : ℝ, ∀ n, l n ≤ s ∧ s ≤ u n
