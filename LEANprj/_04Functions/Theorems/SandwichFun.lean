import LEANprj.defs
import LEANprj._02Sequences.Theorems.SandwichSeq
import LEANprj._04Functions.Theorems.HeineEqCauchy


theorem SandwichFun
  (f g h : ℝ → ℝ) (x₀ q : ℝ)
  (h₁ : f ≤ g) (h₂ : g ≤ h) (h₃ : CauchyLimitFunction f x₀ q ) (h₄ : CauchyLimitFunction h x₀ q) :
  CauchyLimitFunction g x₀ q := by
  rw [← HeineEqCauchy]
  intros s hs s_conv
  have h_f_seq := CauchyImpHeine f x₀ q h₃ s hs s_conv
  have h_h_seq := CauchyImpHeine h x₀ q h₄ s hs s_conv
  have h₁ : f ∘ s ≤ g ∘ s := by exact fun i => h₁ (s i)
  have h₂ : g ∘ s ≤ h ∘ s := by exact fun i => h₂ (s i)
  exact SandwichSeq (f ∘ s) (g ∘ s) (h ∘ s) q h₁ h₂ h_f_seq h_h_seq
