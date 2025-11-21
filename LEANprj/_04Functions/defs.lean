import LEANprj._03Series.defs

def CompactSet (M : Set ℝ) : Prop := ∀ a : ℕ → ℝ, (∀ n : ℕ, a n ∈ M) → ∃ k : ℕ → ℕ, StrictlyIncreasingSequenceN k ∧ Convergent (Subsequence a k)
