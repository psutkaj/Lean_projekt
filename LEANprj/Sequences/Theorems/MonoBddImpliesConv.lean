import LEANprj.Sequences.Theorems.ConvImpliesBdd

theorem MonoBddImpliesConv (a : ℕ → ℝ) (ha_mono : MonotonicSequence a) (ha_bdd : BoundedSequence a) : Convergent a := by
  unfold Convergent
  unfold MonotonicSequence IncreasingSequence DecreasingSequence at ha_mono
  unfold BoundedSequence at ha_bdd
  obtain ⟨s, hs⟩ := SupSeq a
  sorry
