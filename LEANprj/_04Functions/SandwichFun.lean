import LEANprj.defs
import LEANprj._02Sequences.Sandwich
import LEANprj._04Functions.HeineEqCauchy

theorem SandwichFun {a b c : ℝ → ℝ} {x₀ q : ℝ}
  (hab : a ≤ b) (hbc : b ≤ c) (haq : CauchyLimitFunction a x₀ q) (hcq : CauchyLimitFunction c x₀ q) :
  CauchyLimitFunction b x₀ q :=
by
  rw [← HeineEqCauchy]
  intros s hs s_conv
  have has := CauchyImpHeine a x₀ q haq s hs s_conv
  have hcs := CauchyImpHeine c x₀ q hcq s hs s_conv
  have hsab : a ∘ s ≤ b ∘ s := (hab <| s ·)
  have hsbc : b ∘ s ≤ c ∘ s := (hbc <| s ·)
  exact sandwich_seq hsab hsbc has hcs
