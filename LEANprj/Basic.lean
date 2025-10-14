import Mathlib
#eval 2 + 2


def ConvergesTo (a : ℕ → ℝ) (q : ℝ) := ∀ ε > 0, ∃ n₀, ∀ n ≥ n₀, |a n - q| < ε

theorem Sandwich
  (a b c : ℕ → ℝ) (q : ℝ)
  (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : ConvergesTo a q) (h₄ : ConvergesTo c q) :
  ConvergesTo b q :=
by
-- vygenerováno AI (Claude Sonnet 3.7 Thinking)
intro ε hε
rcases h₃ ε hε with ⟨n₁, hn₁⟩
rcases h₄ ε hε with ⟨n₂, hn₂⟩
use max n₁ n₂
intros n hn
have hn₁' : n ≥ n₁ := le_of_max_le_left hn
have hn₂' : n ≥ n₂ := le_of_max_le_right hn
have ha : |a n - q| < ε := hn₁ n hn₁'
have hc : |c n - q| < ε := hn₂ n hn₂'
have ha_bounds : -ε < a n - q ∧ a n - q < ε := abs_lt.mp ha
have hc_bounds : -ε < c n - q ∧ c n - q < ε := abs_lt.mp hc
have hab : a n - q ≤ b n - q := sub_le_sub_right (h₁ n) q
have hbc : b n - q ≤ c n - q := sub_le_sub_right (h₂ n) q
apply abs_lt.mpr
constructor
· exact lt_of_lt_of_le ha_bounds.1 hab
· exact lt_of_le_of_lt hbc hc_bounds.2
