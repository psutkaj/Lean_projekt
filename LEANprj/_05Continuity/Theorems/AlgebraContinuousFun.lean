import LEANprj.defs
import LEANprj._04Functions.Theorems.AlgebraLimitFun
import LEANprj._04Functions.Theorems.HeineEqCauchy

theorem ContinuousAddFun {f g : ℝ → ℝ} (h₁ : FunctionContinuous f) (h₂ : FunctionContinuous g) : FunctionContinuous (f + g) := by
  intro x
  exact LimitAddFunction x (f x) (g x) (h₁ x) (h₂ x)

theorem ContinuousSubFun {f g : ℝ → ℝ} (h₁ : FunctionContinuous f) (h₂ : FunctionContinuous g) : FunctionContinuous (f - g) := by
  intro x
  exact LimitSubFunction x (f x) (g x) (h₁ x) (h₂ x)

theorem ContinuousMulFun {f g : ℝ → ℝ} (h₁ : FunctionContinuous f) (h₂ : FunctionContinuous g) : FunctionContinuous (f * g) := by
  intro x
  exact LimitMulFunction x (f x) (g x) (h₁ x) (h₂ x)

theorem ContinuousDivFun {f g : ℝ → ℝ} (h₁ : FunctionContinuous f) (h₂ : FunctionContinuous g) (h₃ : ∀ x : ℝ, g x ≠ 0) : FunctionContinuous (f / g) := by
  intro x
  exact LimitDivFunction x (f x) (g x) (h₃ x) (h₁ x) (h₂ x)

theorem ContinuousCompFunAt {f g : ℝ → ℝ} (x₀ : ℝ) (h₁ : FunctionContinuousAt f x₀) (h₂ : FunctionContinuousAt g (f x₀)) : FunctionContinuousAt (g ∘ f) x₀ := by
  unfold FunctionContinuousAt
  intro ε ε_pos
  obtain ⟨δ₂, δ₂_pos, hg⟩ := h₂ ε ε_pos
  obtain ⟨δ₁, δ₁_pos, hf⟩ := h₁ δ₂ δ₂_pos
  use δ₁
  constructor
  exact δ₁_pos
  intro x hx
  simp
  specialize hf x hx
  by_cases h_eq : f x = f x₀
  · rw [h_eq]
    ring_nf
    simp
    exact ε_pos
  · apply hg
    constructor
    · exact abs_sub_pos.mpr h_eq
    · exact hf

theorem ContinuousCompFun {f g : ℝ → ℝ} (h₁ : FunctionContinuous f) (h₂ : FunctionContinuous g) : FunctionContinuous (g ∘ f) := by
  unfold FunctionContinuous
  intro x₀
  exact ContinuousCompFunAt x₀ (h₁ x₀) (h₂ (f x₀))
