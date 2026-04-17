import LEANprj.defs

theorem cauchy_of_inc_bdd (a : ℕ → ℝ) (ha_inc : IncreasingSequence a) (ha_bdd : BoundedSequence a) : CauchySequence a := by
  by_contra h_not_cauchy
  unfold CauchySequence at h_not_cauchy
  push_neg at h_not_cauchy

  -- Získáme "zlé" epsilon
  obtain ⟨ε, hε_pos, h_forever⟩ := h_not_cauchy

  -- 2. Příprava: "Skákací lemma"
  -- Dokážeme, že pro každé n existuje m > n, které je o ε výše.
  -- (Negace Cauchy říká, že existují dva indexy daleko od sebe.
  -- Díky monotonii to znamená, že se vzdálíme i od toho našeho n).
  have exists_jump : ∀ n, ∃ m, n < m ∧ a m - a n ≥ ε := by
    intro n
    -- Z negace Cauchyovskosti víme, že pro N=n existují p, q
    obtain ⟨p, q, ⟨hn_p, hn_q⟩, h_dist⟩ := h_forever n

    have h_mono := monotone_nat_of_le_succ ha_inc

    -- Bez újmy na obecnosti ať je p > q (kdyby ne, prohodíme je)
    -- Protože |a p - a q| ≥ ε a posloupnost roste, tak vyšší index minus nižší ≥ ε.
    by_cases h_order : p ≥ q
    · use p
      constructor
      · linarith -- p > n
      · -- a p - a n = (a p - a q) + (a q - a n). Druhá závorka je ≥ 0.
        rw [abs_eq_self.mpr (sub_nonneg.mpr (h_mono h_order))] at h_dist
        have h_growth : a q ≥ a n := h_mono (le_of_lt hn_q)
        linarith
    · -- Případ q > p (analogicky)
      push_neg at h_order
      use q
      constructor
      · linarith
      · rw [abs_sub_comm, abs_eq_self.mpr (sub_nonneg.mpr (h_mono (le_of_lt h_order)))] at h_dist
        have h_growth : a p ≥ a n := h_mono (le_of_lt hn_p)
        linarith

  -- 3. Konstrukce posloupnosti skoků (Axiom výběru)
  -- Vybereme funkci 'next_idx', která pro každé n najde ten skok
  choose next_idx h_jump using exists_jump
  -- h_jump n : n < next_idx n ∧ a (next_idx n) - a n ≥ ε

  -- 4. Definice rekurzivní posloupnosti indexů (Iterace)
  -- steps 0 = 0
  -- steps 1 = next_idx 0
  -- steps 2 = next_idx (next_idx 0) ...
  let steps (k : ℕ) := (next_idx^[k]) 0

  -- 5. Důkaz indukcí, že posloupnost roste do nekonečna ("Schody")
  have h_climb : ∀ k, a (steps k) ≥ a 0 + k * ε := by
    intro k
    induction' k with d hd
    · -- Základní krok (k=0): a 0 ≥ a 0 + 0
      simp [steps]
    · -- Indukční krok:
      -- steps (d+1) je next_idx (steps d)
      -- Víme, že skok mezi nimi je ≥ ε
      specialize h_jump (steps d)
      calc a (steps (d + 1))
        _ = a (next_idx (steps d)) := by simp [steps, Function.iterate_succ_apply']
        _ ≥ a (steps d) + ε        := by linarith [h_jump.2]
        _ ≥ (a 0 + d * ε) + ε      := by linarith [hd]
        _ = a 0 + (d + 1 : ℝ) * ε  := by ring
      simp

  -- 6. Spor s omezeností
  -- Získáme horní závoru K
  obtain ⟨K, _, h_bound⟩ := ha_bdd

  -- Najdeme k dost velké, aby a 0 + k*ε > K (Archimédova vlastnost)
  -- Chceme: k * ε > K - a 0
  have h_arch : ∃ k : ℕ, K - a 0 < k * ε := by
    obtain ⟨k, hk⟩ := exists_nat_gt ((K - a 0) / ε)
    use k
    exact (mul_inv_lt_iff₀ hε_pos).mp hk
  obtain ⟨k, hk_arch⟩ := h_arch

  -- Spor:
  -- Na jedné straně: a (steps k) < K (z omezenosti)
  -- Na druhé straně: a (steps k) > K (ze schodů)
  have h_low := h_bound (steps k)
  rw [abs_le] at h_low

  have h_high : a (steps k) > K := by
    calc a (steps k)
      _ ≥ a 0 + k * ε := h_climb k
      _ > a 0 + (K - a 0) := by linarith [hk_arch]
      _ = K := by ring

  linarith [h_low.2, h_high]
