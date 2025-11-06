import LEANprj.Sequences.sequences

def StrictlyIncreasingSequenceN (a : ℕ → ℕ) := ∀ n : ℕ, a (n + 1) > a n

lemma exSubsequence : ∀ (a : ℕ → ℝ), ∃ k : ℕ → ℕ, StrictlyIncreasingSequenceN k := by
  intro a
  use (λ n => n)
  unfold StrictlyIncreasingSequenceN
  intro n
  linarith

theorem monoSubsequence : ∀ (a : ℕ → ℝ), ∃ k : ℕ → ℕ, StrictlyIncreasingSequenceN k ∧ MonotonicSequence (Subsequence a k) := by
  intro a

  sorry
