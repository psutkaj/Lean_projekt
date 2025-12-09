import LEANprj._01Sets.Theorems.UniquenessOfSupremum
import LEANprj.lemmas
open Classical

lemma IncBddImpliesConv (a : ℕ → ℝ) (ha_inc : IncreasingSequence a) (ha_bdd : BoundedSequence a) : Convergent a := by
  let A := Set.range a
  have A_nonempty : A.Nonempty := by use a 0; tauto
  have A_upper_bdd : UpperBoundedSet A := by
    obtain ⟨k, k_pos, hk⟩ := ha_bdd
    unfold UpperBoundedSet
    use k
    intro m hm
    have : ∀ n : ℕ, a n ∈ A := by intro n; tauto
    simp [A] at hm
    obtain ⟨n, hn⟩ := hm
    calc m
    _ ≤ |m| := le_abs_self m
    _ ≤ k := by rw [←hn]; exact hk n
  obtain ⟨s, ⟨s_upper_bd, s_lub⟩, s_unique⟩ := UniquenessOfSupremum A A_nonempty A_upper_bdd
  use s
  intro ε ε_pos
  obtain ⟨x, xA, hx⟩ := s_lub ε ε_pos
  simp [A] at xA
  obtain ⟨n₀, hn₀⟩ := xA
  use n₀
  intro n hn
  have : a n₀ ≤ a n := by exact inc_le_of_le ha_inc hn
  have : a n ≤ s := by exact s_upper_bd (a n) (by simp [A])
  rw [abs_lt]
  constructor
  · have : s - ε < a n := by calc s - ε
      _ < a n₀ := by rw [hn₀]; exact hx
      _ ≤ a n := by (expose_names; exact this_1)
    exact lt_tsub_iff_left.mpr this
  · have : a n - s ≤ 0 := by linarith
    calc a n - s
    _ ≤ 0 := by linarith
    _ < ε := ε_pos

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
  rcases ha_mono with hinc | hdec
  · exact IncBddImpliesConv a hinc ha_bdd
  · exact DecBddImpliesConv a hdec ha_bdd
