import LEANprj.Sequences.defs

theorem Sandwich
  (a b c : ℕ → ℝ) (q : ℝ)
  (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : ConvergesTo a q) (h₄ : ConvergesTo c q) :
  ConvergesTo b q :=
by
  intro ε ε_pos
    -- zavedu si ε a hyp o tom, že ε > 0
  obtain ⟨n₁, han⟩ := h₃ ε ε_pos
    -- z hyp h₃ a předp, že ε > 0 získám index n₁ a hyp han o konvergenci a k q od indexu n₁
  obtain ⟨n₂, hcn⟩ := h₄ ε ε_pos
    -- z hyp h₄ a předp, že ε > 0 získám index n₂ a hyp hcn o konvergenci c k q od indexu n₂
  let n₀ := max n₁ n₂
    -- zvolím maximum z těchto dvou jako n₀
  use n₀
    -- a budu v dk pokračovat pro n₀ už pevně dané
  intros n hn
    -- zavedu si n ∈ ℕ a hyp hn, že n ≥ n₀
  have ha_appl := han n (le_trans (le_max_left _ _) hn)
    -- aplikuju han v indexu n, tj. |a n - q| < ε,
    -- a potřebuji dokázat, že n ≥ n₁ (víme, protože beru maximum ze dvou)
  have hc_appl := hcn n (le_trans (le_max_right _ _) hn)
    -- obdobně pro hcn v indexu n, tj. |c n - q| < ε, důkaz beru pro n₂
  rw [abs_lt]
  rw [abs_lt] at ha_appl
  rw [abs_lt] at hc_appl
    -- rozeberu v těchto třech případech absolutní hodnotu v nerovnosti na dva případy
    -- a v cíli získám konjukci
  have ha_lower  : q - ε < a n   := by linarith
    -- pomocné tvrzení q - ε < a n, získám upravením z ha_appl.left
  have hc_upper  : c n < q + ε   := by linarith
    -- c n < q + ε, získám upravením z hc_appl.right
  have hb_lower1 : q - ε < b n   := by exact lt_of_lt_of_le ha_lower (h₁ n)
    -- dolní hranice pro b n, q - ε < b n, získám z nerovnosti ha_lower a h₁ (a ≤ b)
  have hb_lower2 : - ε < b n - q := by linarith
    -- úprava předchozího na požadovaný tvar
  have hb_upper1 : b n < q + ε   := by exact lt_of_le_of_lt (h₂ n) hc_upper
    -- horní hranice pro b n, b n < q + ε, získám z nerovnosti hc_upper a h₂ (b ≤ c)
  have hb_upper2 : b n - q < ε   := by linarith
    -- úprava předchozího na požadovaný tvar
  exact ⟨hb_lower2, hb_upper2⟩
    -- cíl je přesně jako kombinace hb_lower2 a hb_upper2
