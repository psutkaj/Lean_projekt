import LEANprj.defs
import LEANprj._02Sequences.Sandwich
import LEANprj._03Functions.HeineIffCauchy

theorem sandwich_fun {a b c : ℝ → ℝ} {x₀ q : ℝ}
  (hab : a ≤ b) (hbc : b ≤ c) (haq : CauchyLimitFun a x₀ q) (hcq : CauchyLimitFun c x₀ q) :
  CauchyLimitFun b x₀ q :=
by
  rw [← heine_iff_cauchy]
  intros s hs s_conv
  have has := heine_of_cauchy a x₀ q haq s hs s_conv
  have hcs := heine_of_cauchy c x₀ q hcq s hs s_conv
  have hsab : a ∘ s ≤ b ∘ s := (hab <| s ·)
  have hsbc : b ∘ s ≤ c ∘ s := (hbc <| s ·)
  exact sandwich_seq hsab hsbc has hcs
