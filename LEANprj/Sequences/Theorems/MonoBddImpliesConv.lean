import LEANprj.Sequences.sequences
open Classical

lemma IncBddImpliesConv (a : ℕ → ℝ) (ha_inc : IncreasingSequence a) (ha_bdd : BoundedSequence a) : Convergent a := by
  unfold Convergent
  unfold IncreasingSequence at ha_inc
  unfold BoundedSequence at ha_bdd
  obtain ⟨K, hK, K_bd⟩ := ha_bdd
  let A : Set ℝ := Set.range a
  let s : ℝ := SupSeq a (by use K; intro n; exact lt_of_abs_lt (K_bd n) )
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
  have : a N ≤ a m := by exact inc_le_of_le ha_inc hm
  have lower' : s - ε < a m := by exact lt_of_le_of_lt' this hN
  have upper' : a m ≤ s := by
    obtain ⟨le_s, s_lt⟩ := hsup (a m) (by tauto)
    exact le_s
  have : |a m - s| < ε := by
    have h₁ : s - a m < ε := by linarith
    have h₂ : s - a m ≥ 0 := by linarith
    have h₃ : s - a m = |s - a m| := by exact Eq.symm (abs_of_nonneg h₂)
    calc
      |a m - s| = |s - a m| := by exact abs_sub_comm (a m) s
      |s - a m| = s - a m := by exact id (Eq.symm h₃)
      _ < ε := by exact h₁
  exact this

lemma DecBddImpliesConv (a : ℕ → ℝ) (ha_dec : DecreasingSequence a) (ha_bdd : BoundedSequence a) : Convergent a := by
  unfold Convergent
  unfold DecreasingSequence at ha_dec
  unfold BoundedSequence at ha_bdd
  obtain ⟨K, hK, K_bd⟩ := ha_bdd

  let b := λ n => -(a n)
  have b_eq_neg_a : ∀ n, b n = - a n := by exact fun n => rfl
  have b_inc : IncreasingSequence b := by
    unfold IncreasingSequence
    intro n
    rw [b_eq_neg_a n]
    rw [b_eq_neg_a (n+1)]
    exact neg_le_neg_iff.mpr (ha_dec n)
  have b_bdd : BoundedSequence b := by
    unfold BoundedSequence
    refine ⟨K, hK, ?_⟩
    intro n
    rw [b_eq_neg_a n]
    have : |(-a n)| = |a n| := by exact abs_neg (a n)
    rw [this]
    exact K_bd n

  have : Convergent b := by exact IncBddImpliesConv b b_inc b_bdd
  obtain ⟨q, hq⟩ := this
  use -q
  unfold ConvergesTo
  intro ε ε_pos
  obtain ⟨n₀, hn₀⟩ := hq ε ε_pos
  use n₀
  intro n₁ hn₁
  simp
  have : |a n₁ + q| = |-(a n₁) - q| := by
    calc
    |a n₁ + q| = |-1| * |a n₁ + q| := by simp
    _ = |(-1) * (a n₁ + q)| := by exact Eq.symm (abs_mul (-1) (a n₁ + q))
    _ = |- (a n₁) - q| := by ring_nf
  rw [this]
  rw [← b_eq_neg_a n₁]
  exact hn₀ n₁ hn₁

theorem MonoBddImpliesConv (a : ℕ → ℝ) (ha_mono : MonotonicSequence a) (ha_bdd : BoundedSequence a) : Convergent a := by
  -- rozdelime na dva pripady podle monotonie
  rcases ha_mono with hinc | hdec
  · exact IncBddImpliesConv a hinc ha_bdd
  · exact DecBddImpliesConv a hdec ha_bdd
