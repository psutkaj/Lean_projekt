import LEANprj.defs
import LEANprj._03Functions.AlgebraLimitFun
import LEANprj._03Functions.HeineIffCauchy

namespace ContFun

theorem add {f g : ℝ → ℝ} (hf : FunContinuous f) (hg : FunContinuous g) : FunContinuous (f + g) := by
  intro x
  exact LimitFun.add (hf x) (hg x)

theorem sub {f g : ℝ → ℝ} (hf : FunContinuous f) (hg : FunContinuous g) : FunContinuous (f - g) := by
  intro x
  exact LimitFun.sub (hf x) (hg x)

theorem mul {f g : ℝ → ℝ} (hf : FunContinuous f) (hg : FunContinuous g) : FunContinuous (f * g) := by
  intro x
  exact LimitFun.mul (hf x) (hg x)

theorem div {f g : ℝ → ℝ} (hf : FunContinuous f) (hg : FunContinuous g) (h0 : ∀ x : ℝ, g x ≠ 0) : FunContinuous (f / g) := by
  intro x
  exact LimitFun.div (h0 x) (hf x) (hg x)

theorem comp_at {f g : ℝ → ℝ} (x₀ : ℝ)
  (hf : FunContinuousAt f x₀)
  (hg : FunContinuousAt g (f x₀)) :
  FunContinuousAt (g ∘ f) x₀ :=
by
  intro ε ε_pos
  obtain ⟨δ₂, δ₂_pos, hg⟩ := hg ε ε_pos
  obtain ⟨δ₁, δ₁_pos, hf⟩ := hf δ₂ δ₂_pos
  use δ₁, δ₁_pos
  intro x hx
  simp only [Function.comp_apply]
  by_cases h_eq : f x = f x₀
  · simpa [h_eq, sub_self] using ε_pos
  · apply hg
    exact ⟨abs_sub_pos.mpr h_eq, hf x hx⟩

theorem comp {f g : ℝ → ℝ} (hf : FunContinuous f) (hg : FunContinuous g) : FunContinuous (g ∘ f) := by
  intro x₀
  exact comp_at x₀ (hf x₀) (hg (f x₀))

end ContFun
