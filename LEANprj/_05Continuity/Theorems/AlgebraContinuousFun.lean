import LEANprj.defs
import LEANprj._04Functions.Theorems.AlgebraLimitFun
import LEANprj._04Functions.Theorems.HeineEqCauchy

theorem ContinuousAddFun {f g : ℝ → ℝ} (hf : FunctionContinuous f) (hg : FunctionContinuous g) : FunctionContinuous (f + g) := by
  intro x
  exact LimitAddFunction (hf x) (hg x)

theorem ContinuousSubFun {f g : ℝ → ℝ} (hf : FunctionContinuous f) (hg : FunctionContinuous g) : FunctionContinuous (f - g) := by
  intro x
  exact LimitSubFunction (hf x) (hg x)

theorem ContinuousMulFun {f g : ℝ → ℝ} (hf : FunctionContinuous f) (hg : FunctionContinuous g) : FunctionContinuous (f * g) := by
  intro x
  exact LimitMulFunction (hf x) (hg x)

theorem ContinuousDivFun {f g : ℝ → ℝ} (hf : FunctionContinuous f) (hg : FunctionContinuous g) (h0 : ∀ x : ℝ, g x ≠ 0) : FunctionContinuous (f / g) := by
  intro x
  exact LimitDivFunction (h0 x) (hf x) (hg x)

theorem ContinuousCompFunAt {f g : ℝ → ℝ} (x₀ : ℝ) (hf : FunctionContinuousAt f x₀) (hg : FunctionContinuousAt g (f x₀)) : FunctionContinuousAt (g ∘ f) x₀ := by
  unfold FunctionContinuousAt
  intro ε ε_pos
  obtain ⟨δ₂, δ₂_pos, hg⟩ := hg ε ε_pos
  obtain ⟨δ₁, δ₁_pos, hf⟩ := hf δ₂ δ₂_pos
  use δ₁
  constructor
  exact δ₁_pos
  intro x hx
  simp only [Function.comp_apply]
  specialize hf x hx
  by_cases h_eq : f x = f x₀
  · rw [h_eq, sub_self]
    simpa using ε_pos
  · apply hg
    constructor
    · exact abs_sub_pos.mpr h_eq
    · exact hf

theorem ContinuousCompFun {f g : ℝ → ℝ} (hf : FunctionContinuous f) (hg : FunctionContinuous g) : FunctionContinuous (g ∘ f) := by
  unfold FunctionContinuous
  intro x₀
  exact ContinuousCompFunAt x₀ (hf x₀) (hg (f x₀))
