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
    have : a N ≤ a m := by exact inc_le_of_le hinc hm
    have lower' : s - ε < a m := by exact lt_of_le_of_lt' this hN
    have upper' : a m ≤ s := by
      obtain ⟨le_s, s_lt⟩ := hsup (a m) (by tauto)
      exact le_s
    have : |a m - s| < ε := by
      --have : s - ε < a m ∧ a m ≤ s := ⟨lower', upper'⟩
      have h₁ : s - a m < ε := by linarith
      have h₂ : s - a m ≥ 0 := by linarith
      have h₃ : s - a m = |s - a m| := by exact Eq.symm (abs_of_nonneg h₂)
      calc
        |a m - s| = |s - a m| := by exact abs_sub_comm (a m) s
        |s - a m| = s - a m := by exact id (Eq.symm h₃)
        _ < ε := by exact h₁
    exact this
  · sorry
