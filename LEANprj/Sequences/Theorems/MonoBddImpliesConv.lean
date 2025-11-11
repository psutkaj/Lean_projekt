import LEANprj.Sequences.sequences
open Classical

theorem MonoBddImpliesConv (a : ℕ → ℝ) (ha_mono : MonotonicSequence a) (ha_bdd : BoundedSequence a) : Convergent a := by
  unfold Convergent
  unfold MonotonicSequence IncreasingSequence DecreasingSequence at ha_mono
  unfold BoundedSequence at ha_bdd
  obtain ⟨K, hK, K_bd⟩ := ha_bdd
  let A : Set ℝ := Set.range a
  -- rozdelime na dva pripady podle monotonie
  rcases ha_mono with hinc | hdec
  · let s : ℝ := SupSeq a (by use K; intro n; exact lt_of_abs_lt (K_bd n))
    use s
    unfold ConvergesTo
    intro ε ε_pos
    have hsup : IsSup A s := by
      exact SupSeq_IsSup a (Exists.intro K fun n => lt_of_abs_lt (K_bd n))
    have hexn : ∃ n, s - ε < a n := by
      obtain ⟨_, hε⟩ := hsup (a 0) (by tauto)
      obtain ⟨x, hxA, hxgt⟩ := hε ε ε_pos
      obtain ⟨n, rfl⟩ := hxA
      exact ⟨n, hxgt⟩
    obtain ⟨N, hN⟩ := hexn
    use N
    intro m hm
    have : a N ≤ a m := by

      sorry
    sorry
  · sorry
