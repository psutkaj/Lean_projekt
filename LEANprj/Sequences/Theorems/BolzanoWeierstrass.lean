import LEANprj.Sequences.Theorems.monoBddImpliesConv
import LEANprj.Sequences.Theorems.ExMonoSubsequence

theorem BolzanoWeierstrass (a : ℕ → ℝ) (ha_bdd : BoundedSequence a) : ∃ k : ℕ → ℕ, StrictlyIncreasingSequenceN k ∧ Convergent (Subsequence a k) := by
  obtain ⟨k, hk_inc, hk_mono⟩ := monoSubsequence a
  use k
  have sub_bdd : BoundedSequence (Subsequence a k) := by
    unfold BoundedSequence Subsequence
    obtain ⟨K, hK, hkn⟩ := ha_bdd
    refine ⟨K, hK, ?_⟩
    intro n
    exact hkn (k n)
  constructor
  · exact hk_inc
  · exact MonoBddImpliesConv (Subsequence a k) hk_mono sub_bdd
