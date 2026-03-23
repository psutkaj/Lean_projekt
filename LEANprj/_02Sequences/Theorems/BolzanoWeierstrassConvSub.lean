import LEANprj._02Sequences.Theorems.MonoBddImpliesConv
import LEANprj._02Sequences.Theorems.ExMonoSubsequence

theorem bolzano_weierstrass_conv_subsequence (a : Sequence) (ha_bdd : BoundedSequence a) : ∃ k : ℕ → ℕ, StrictlyIncreasingSequenceN k ∧ Convergent (Subsequence a k) := by
  obtain ⟨k, hk_inc, hk_mono⟩ := ex_mono_subsequence a
  use k, hk_inc
  have sub_bdd : BoundedSequence (Subsequence a k) := by
    obtain ⟨K, hK, hKn⟩ := ha_bdd
    use K, hK
    intro n
    exact hKn (k n)
  exact mono_bdd_imp_conv (Subsequence a k) hk_mono sub_bdd
