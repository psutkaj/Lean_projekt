import LEANprj.defs
import LEANprj._05Continuity.Theorems.AlgebraContinuousFun
import LEANprj._05Continuity.Theorems.IntermediateValue
import LEANprj._04Functions.Theorems.UniquenessFun
import LEANprj._04Functions.Theorems.SandwichFun
import LEANprj._02Sequences.Theorems.BolzanoWeierstrass

theorem WeierstrassBdd
  (f : ℝ → ℝ) (a b : ℝ) (h_ab : a ≤ b) (Int : Set ℝ) (hInt : Int = Set.Icc a b)
  (h_cont : FunctionContinuousOnSet Int f) :
  FunctionBddOnSet Int f := by
  by_contra h_unbdd
  unfold FunctionBddOnSet at h_unbdd
  push_neg at h_unbdd
  let x_seq : ℕ → ℝ := λ n => Classical.choose (h_unbdd (n + 1) (by linarith))
  have h_x_seq_prop : ∀ n, x_seq n ∈ Int ∧ |f (x_seq n)| ≥ n + 1 := fun n => Classical.choose_spec (h_unbdd (n + 1) (by linarith))
  have h_x_seq_bounded : BoundedSequence x_seq := by
    unfold BoundedSequence
    let K := max (|a| + |b| + 1) 1
    use K, by dsimp [K]; simp
    intro n
    have h := (h_x_seq_prop n).1
    rw [hInt] at h
    simp at h
    cases' h with h_left h_right
    rw [abs_lt]
    dsimp [K]
    constructor
    · calc -max (|a| + |b| + 1) 1
      _ ≤ - (|a| + |b| + 1) := neg_le_neg (le_max_left _ _)
      _ < -|a| := by
        simp
        refine neg_lt_iff_pos_add'.mpr ?_
        have : |b| ≥ 0 := abs_nonneg b
        calc 0 < 1 := Real.zero_lt_one
        _ ≤ |b| + 1 := by exact le_add_of_nonneg_left this
      _ ≤ a := by exact neg_abs_le a
      _ ≤ x_seq n := h_left
    · calc x_seq n
        _ ≤ b := h_right
        _ < |b| + 1 := by
          have : b ≤ |b| := le_abs_self b
          linarith
        _ ≤ |a| + |b| + 1 := by simp
        _ ≤ K := by dsimp [K]; simp
  obtain ⟨k, hk_inc, c, hk_conv⟩ := BolzanoWeierstrass x_seq h_x_seq_bounded
  have hc_in_Int : c ∈ Int := by
    rw [hInt]
    simp
    have h_closure : ∀ n, x_seq (k n) ∈ Int := by
      intro n
      exact (h_x_seq_prop (k n)).1
    constructor
    · by_contra hnot
      push_neg at hnot
      let ε := (a - c) / 2
      have ε_pos : ε > 0 := by dsimp[ε]; linarith
      obtain ⟨n₀, hn₀⟩ := hk_conv ε ε_pos
      specialize hn₀ n₀ (by linarith)
      rw [hInt] at h_closure
      have h_x_ge_a := (h_closure n₀).1
      rw [Subsequence] at hn₀
      simp at hn₀
      have upper_bound : c + ε = (a + c)/2 := by ring
      have upper_bound_lt_a : (a + c)/2 < a := by linarith
      rw [abs_lt] at hn₀
      have h_x_lt_a : x_seq (k n₀) < a := by linarith
      linarith
    · by_contra hnot
      push_neg at hnot
      let ε := (c - b) / 2
      have ε_pos : ε > 0 := by dsimp [ε]; linarith
      have hε : ε > 0 := by linarith
      obtain ⟨N, hN⟩ := hk_conv ε hε
      specialize hN N (by linarith)
      rw [hInt] at h_closure
      have h_x_le_b := (h_closure N).2
      rw [Subsequence] at hN
      simp at hN
      rw [abs_lt] at hN
      have lower_bound : c - ε = (b + c)/2 := by ring
      have upper_bound_lt_a : (b + c)/2 > b := by linarith
      linarith



  sorry

axiom WeierstrassMax
  (f : ℝ → ℝ) (a b : ℝ) (h_ab : a ≤ b) (Int : Set ℝ) (hInt : Int = Set.Icc a b)
  (h_cont : FunctionContinuousOnSet Int f) :
  ∃ M ∈ Int, ∀ x ∈ Int, f x ≤ f M

theorem WeierstrassMin
  (f : ℝ → ℝ) (a b : ℝ) (h_ab : a ≤ b) (Int : Set ℝ) (hInt : Int = Set.Icc a b)
  (h_cont : FunctionContinuousOnSet Int f) :
  ∃ m ∈ Int, ∀ x ∈ Int, f m ≤ f x := by
  let g := λ x ↦ - f x
  have g_cont : FunctionContinuousOnSet Int g := by
    intro x hx
    unfold FunctionContinuousAt CauchyLimitFunction
    intro ε ε_pos
    obtain ⟨δ, δ_pos, hδ⟩ := h_cont x hx ε ε_pos
    use δ, δ_pos
    intro x₁ hx₁
    dsimp [g]
    simp
    specialize hδ x₁ hx₁
    have : |f x₁ - f x| = |-f x₁ + f x| := by calc |f x₁ - f x|
      _ = |-1| * |f x₁ - f x| := by simp
      _ = |(-1) * (f x₁ - f x)| := by exact Eq.symm (abs_mul (-1) (f x₁ - f x))
      _ = |- f x₁ + f x| := by ring_nf
    rw [←this]
    exact hδ
  obtain ⟨m, hm, m_leq⟩ := WeierstrassMax g a b h_ab Int hInt g_cont
  use m, hm
  intro x hx
  specialize m_leq x hx
  dsimp [g] at m_leq
  linarith

theorem WeierstrassExtremeValue
  (f : ℝ → ℝ) (a b : ℝ) (h_ab : a ≤ b) (Int : Set ℝ) (hInt : Int = Set.Icc a b)
  (h_cont : FunctionContinuousOnSet Int f) :
  (FunctionBddOnSet Int f) ∧
  (∃ M ∈ Int, ∀ x ∈ Int, f x ≤ f M) ∧
  (∃ m ∈ Int, ∀ x ∈ Int, f m ≤ f x) := by
  exact ⟨WeierstrassBdd f a b h_ab Int hInt h_cont, WeierstrassMax f a b h_ab Int hInt h_cont, WeierstrassMin f a b h_ab Int hInt h_cont⟩
