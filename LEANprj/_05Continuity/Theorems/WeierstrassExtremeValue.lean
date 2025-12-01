import LEANprj.defs
import LEANprj._05Continuity.Theorems.AlgebraContinuousFun
import LEANprj._05Continuity.Theorems.IntermediateValue
import LEANprj._04Functions.Theorems.UniquenessFun
import LEANprj._04Functions.Theorems.SandwichFun
import LEANprj._02Sequences.Theorems.BolzanoWeierstrass

lemma ContinuousImageBounded
  (f : ℝ → ℝ) (a b : ℝ) (h_ab : a ≤ b)
  (h_cont : ∀ x ∈ Set.Icc a b, FunctionContinuousAt f x) :
  ∃ B : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ B := by

  sorry

axiom WeierstrassMax
  (f : ℝ → ℝ) (a b : ℝ) (h_ab : a ≤ b)
  (h_cont : ∀ x ∈ Set.Icc a b, FunctionContinuousAt f x) :
  ∃ M ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f x ≤ f M

theorem WeierstrassMin
  (f : ℝ → ℝ) (a b : ℝ) (h_ab : a ≤ b)
  (h_cont : ∀ x ∈ Set.Icc a b, FunctionContinuousAt f x) :
  ∃ m ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f m ≤ f x := by
  let g := λ x ↦ - f x
  have g_cont : ∀ x ∈ Set.Icc a b, FunctionContinuousAt g x := by
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
  obtain ⟨m, hm, m_leq⟩ := WeierstrassMax g a b h_ab g_cont
  use m, hm
  intro x hx
  specialize m_leq x hx
  dsimp [g] at m_leq
  linarith

theorem WeierstrassExtremeValue
  (f : ℝ → ℝ) (a b : ℝ) (h_ab : a ≤ b)
  (h_cont : ∀ x ∈ Set.Icc a b, FunctionContinuousAt f x) :
  (∃ M ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f x ≤ f M) ∧
  (∃ m ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f m ≤ f x) := by
  exact ⟨WeierstrassMax f a b h_ab h_cont, WeierstrassMin f a b h_ab h_cont⟩
