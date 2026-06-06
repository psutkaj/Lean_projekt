import LEANprj.defs
import LEANprj._02Sequences.AlgebraLimit
import LEANprj._03Functions.HeineIffCauchy

namespace LimitFun

theorem add {f g : ℝ → ℝ} {x₀ b c : ℝ}
  (hfb : CauchyLimitFun f x₀ b) (hgc : CauchyLimitFun g x₀ c) :
  CauchyLimitFun (f + g) x₀ (b + c) :=
by
  rw [←heine_iff_cauchy] at *
  intro x x_ne x_conv
  specialize hfb x x_ne x_conv
  specialize hgc x x_ne x_conv
  apply convergesTo.add hfb hgc

theorem sub {f g : ℝ → ℝ} {x₀ b c : ℝ}
  (hfb : CauchyLimitFun f x₀ b) (hgc : CauchyLimitFun g x₀ c) :
  CauchyLimitFun (f - g) x₀ (b - c) :=
by
  unfold CauchyLimitFun at *
  intros ε₀ ε₀_pos
  let ε := ε₀ / 2
  have ε_pos : ε > 0 := half_pos ε₀_pos
  specialize hfb ε ε_pos
  specialize hgc ε ε_pos
  obtain ⟨δ₁, δ₁_pos, h₁⟩ := hfb
  obtain ⟨δ₂, δ₂_pos, h₂⟩ := hgc
  let δ := min δ₁ δ₂
  have δ_pos : δ > 0 := lt_min δ₁_pos δ₂_pos
  refine ⟨δ, δ_pos, ?_⟩
  intro x hx
  rw [Pi.sub_apply]
  have hδ₁ : δ ≤ δ₁ := min_le_left δ₁ δ₂
  have hδ₂ : δ ≤ δ₂ := min_le_right δ₁ δ₂
  have : 0 < |x - x₀| ∧ |x - x₀| < δ₁ := by
    constructor
    · linarith
    · calc
        |x - x₀| < δ := hx.2
        _ ≤ δ₁ := hδ₁
  have ha := h₁ x this
  have : 0 < |x - x₀| ∧ |x - x₀| < δ₂ := by
    constructor
    · linarith
    · calc
        |x - x₀| < δ := hx.2
        _ ≤ δ₂ := hδ₂
  have hb := h₂ x this
  calc
    |f x - g x - (b - c)| = |f x - b + (-1) * (g x - c)| := by ring_nf
    _ ≤ |f x - b| + |-1 * (g x - c)| := by apply abs_add _ _
    _ = |f x - b| + |g x - c| := by simpa using abs_sub_comm c (g x)
    _ < ε + ε := add_lt_add ha hb
    _ = ε₀ := by ring

theorem mul {f g : ℝ → ℝ} {x₀ b c : ℝ}
  (hfb : CauchyLimitFun f x₀ b) (hgc : CauchyLimitFun g x₀ c) :
  CauchyLimitFun (f * g) x₀ (b * c) :=
by
  rw [←heine_iff_cauchy]
  intros s hs s_conv
  have h_f_seq := heine_of_cauchy f x₀ b hfb s hs s_conv
  have h_g_seq := heine_of_cauchy g x₀ c hgc s hs s_conv
  exact convergesTo.mul h_f_seq h_g_seq

theorem div {f g : ℝ → ℝ} {x₀ b c : ℝ} (h_cne : c ≠ 0)
  (hfb : CauchyLimitFun f x₀ b) (hgc : CauchyLimitFun g x₀ c) :
  CauchyLimitFun (f / g) x₀ (b / c) :=
by
  rw [←heine_iff_cauchy]
  intros s hs s_conv
  have h_f_seq := heine_of_cauchy f x₀ b hfb s hs s_conv
  have h_g_seq := heine_of_cauchy g x₀ c hgc s hs s_conv
  exact convergesTo.div h_cne h_f_seq h_g_seq

end LimitFun
