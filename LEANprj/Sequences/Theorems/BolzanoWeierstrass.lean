import LEANprj.Sequences.Theorems.monoBddImpliesConv
import LEANprj.Sequences.Theorems.ExMonoSubsequence

theorem BolzanoWeierstrass (a : ℕ → ℝ) (haBdd : BoundedSequence a) : ∃ k : ℕ → ℕ, StrictlyIncreasingSequenceN k ∧ Convergent (Subsequence a k) := by
  sorry
