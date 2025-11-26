import LEANprj._02Sequences.Theorems.MonoBddImpliesConv
import LEANprj._02Sequences.Theorems.ExMonoSubsequence

theorem BolzanoWeierstrass (a : ℕ → ℝ) (ha_bdd : BoundedSequence a) : ∃ k : ℕ → ℕ, StrictlyIncreasingSequenceN k ∧ Convergent (Subsequence a k) := by
  obtain ⟨k, hk_inc, hk_mono⟩ := ExMonoSubsequence a
  have sub_bdd : BoundedSequence (Subsequence a k) := by
    obtain ⟨K, hK, hkn⟩ := ha_bdd
    refine ⟨K, hK, ?_⟩
    intro n
    exact hkn (k n)
  refine ⟨k, hk_inc, ?_⟩
  exact MonoBddImpliesConv (Subsequence a k) hk_mono sub_bdd
