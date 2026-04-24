import LEANprj._01Sets.AxSupOfAxNIP
import LEANprj.lemmas
open Classical

lemma convergesTo_of_bdd_inc (a : ℕ → ℝ) :
  AxSup →
  IncreasingSequence a →
  BoundedSequence a →
  Convergent a :=
by
  intro AxSup a_inc a_bdd
  let A := Set.range a
  have A_nonempty : A.Nonempty := by use a 0; tauto
  have A_upper_bdd : UpperBoundedSet A := by
    obtain ⟨k, k_pos, hk⟩ := a_bdd
    unfold UpperBoundedSet
    use k
    intro m hm
    have : ∀ n : ℕ, a n ∈ A := by intro n; tauto
    simp [A] at hm
    obtain ⟨n, hn⟩ := hm
    calc m
    _ ≤ |m| := le_abs_self m
    _ ≤ k := by rw [←hn]; exact hk n
  obtain ⟨s, ⟨s_upper_bd, s_lub⟩, s_unique⟩ := AxSup A A_nonempty A_upper_bdd
  use s
  intro ε ε_pos
  obtain ⟨x, xA, hx⟩ := s_lub ε ε_pos
  simp [A] at xA
  obtain ⟨n₀, hn₀⟩ := xA
  use n₀
  intro n hn
  have h₁ : a n₀ ≤ a n := inc_le_of_le a_inc hn
  have h₂ : a n ≤ s := s_upper_bd (a n) (by simp [A])
  rw [abs_lt]
  constructor
  · have : s - ε < a n := by calc s - ε
      _ < a n₀ := by rw [hn₀]; exact hx
      _ ≤ a n := h₁
    exact lt_tsub_iff_left.mpr this
  · have : a n - s ≤ 0 := by linarith
    calc a n - s
    _ ≤ 0 := by linarith
    _ < ε := ε_pos

lemma convergesTo_of_bdd_dec (a : ℕ → ℝ) :
  AxSup →
  DecreasingSequence a →
  BoundedSequence a →
  Convergent a :=
by
  intro AxSup a_dec a_bdd
  obtain ⟨K, hK, K_bd⟩ := a_bdd
  let b := λ n => -(a n)
  have b_eq_neg_a : ∀ n, b n = - a n := λ n => rfl
  have b_inc : IncreasingSequence b := by
    intro n
    rw [b_eq_neg_a n]
    rw [b_eq_neg_a (n+1)]
    exact neg_le_neg_iff.mpr (a_dec n)
  have b_bdd : BoundedSequence b := by
    use K, hK
    intro n
    rw [b_eq_neg_a n]
    have : |(-a n)| = |a n| := abs_neg (a n)
    rw [this]
    exact K_bd n
  have : Convergent b := convergesTo_of_bdd_inc b AxSup b_inc b_bdd
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
    _ = |(-1) * (a n₁ + q)| := Eq.symm (abs_mul (-1) (a n₁ + q))
    _ = |- (a n₁) - q| := by ring_nf
  rw [this]
  rw [← b_eq_neg_a n₁]
  exact hn₀ n₁ hn₁

theorem axMonoConv_of_axSup :
  AxSup →
  AxMonoConv :=
by
  intro AxSup a a_mono a_bdd
  rcases a_mono with a_inc | a_dec
  · exact convergesTo_of_bdd_inc a AxSup a_inc a_bdd
  · exact convergesTo_of_bdd_dec a AxSup a_dec a_bdd
