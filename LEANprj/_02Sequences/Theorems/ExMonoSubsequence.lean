import LEANprj._02Sequences.defs
open Classical



private def Peak (a : ℕ → ℝ) (n : ℕ) : Prop := ∀ {m : ℕ}, n < m → a m ≤ a n

lemma peak_iff (a : ℕ → ℝ) (n : ℕ) : Peak a n ↔ ∀ m > n, a m ≤ a n := by
  rfl

lemma not_peak_iff_exists_gt (a : ℕ → ℝ) (n : ℕ) : ¬ Peak a n ↔ ∃ m, n < m ∧ a n < a m := by
  unfold Peak
  push_neg
  rfl

-- z nekonecnosti P ∀ t ∈ P ∃ m ∈ P : t < m, tj. vzdy ∃ m ∈ P vetsi nez t
lemma exists_mem_P_gt_of_infinite (P : Set ℕ) (hInf : P.Infinite) (t : ℕ) : ∃ m, m ∈ P ∧ t < m := by
  -- kdyby neexistovalo m > t v P, pak P by byla omezena tim t, a tedy P je konecna — spor.
  by_contra h
  push_neg at h   -- h : ∀ m ∈ P : m ≤ t
  -- P ⊆ (-∞, t⟩
  have hsub : P ⊆ Set.Iic t := by
    intro m hmP
    exact h m hmP
  -- podmnozina ℕ omezena prvkem t je konecna
  have hfin_Iic : (Set.Iic t : Set ℕ).Finite := by exact Set.finite_Iic t
  -- a tedy P je konecna
  have hfinP : P.Finite := hfin_Iic.subset hsub
  -- coz je spor
  exact hInf hfinP


-- Věta: Z každé posloupnosti v ℝ lze vybrat monotonní podposloupnost.
theorem monoSubsequence : ∀ (a : ℕ → ℝ), ∃ k : ℕ → ℕ, StrictlyIncreasingSequenceN k ∧ MonotonicSequence (Subsequence a k) := by
  intro a
  -- zavedeme mnozinu Peaks
  let P : Set ℕ := {n | Peak a n}

  -- a mame dva pripady, bud je P nekonecna nebo ne
  by_cases hInf : P.Infinite
  · -- pro pripad, ze P je nekonecna, tj mam nekonecne mnoho Peak pointu, tak si vzdy do podposloupnosti volim prave tyto body
    -- z definice peak pointu je tato posloupnost kleasiji a tedy monotonni

    -- vybereme si svedka k : ℕ → ℕ, ostre rostouciho a k ⊆ P
    obtain ⟨k, k_strict_inc, k_in_P⟩ : ∃ k : ℕ → ℕ, StrictlyIncreasingSequenceN k ∧ ∀ n, k n ∈ P := by
      -- vzdy mame dalsi krok
      have step : ∀ t : ℕ, ∃ m, m ∈ P ∧ t < m := by
        intro t
        -- coz uz mame dokazane z nekonecnosti P
        exact exists_mem_P_gt_of_infinite P hInf t

      -- vezmeme si funkci nalsedovnika t
      choose next hnext_mem hnext_gt using step

      -- zkonstruujeme k : ℕ → ℕ rekurzivne pomoci next
      let k : ℕ → ℕ := Nat.rec (next 0) (fun n kn => next kn)
      have k_zero : k 0 = next 0 := by simp [k]
      have k_succ (n) : k (n+1) = next (k n) := by simp [k]

      -- a ukazeme ze je ostre rostouci
      have k_strict_inc : StrictlyIncreasingSequenceN k := by
        unfold StrictlyIncreasingSequenceN
        intro n
        simpa [k_succ n] using hnext_gt (k n)

      -- a ze je podmnozinou P
      have k_in_P : ∀ n, k n ∈ P := by
        intro n
        induction' n with i ih
        · rw [k_zero]
          exact hnext_mem 0
        · rw [k_succ]
          exact hnext_mem (k i)
      exact ⟨k, k_strict_inc, k_in_P⟩

    -- ted tedy mam uz vyrobenou k : ℕ → ℕ ostre rostouci a kazdy prvek je Peakpoint
    -- potrebuji jeste ukazat je podposloupnost s nasi k je klesajici
    have h_dec : MonotonicSequence (Subsequence a k) := by
      unfold MonotonicSequence
      right
      unfold DecreasingSequence Subsequence
      intro n
      -- vime, ze kazdy clen podposloupnosti je Peak
      have hpeak : Peak a (k n) := by exact k_in_P n
      unfold Peak at hpeak
      -- potrebujeme pro dalsi krok jen ukazat toto
      have k_inc : k n < k (n + 1) := by exact k_strict_inc n
      -- a do hpeak dosadime za m = n + 1
      specialize hpeak k_inc
      exact hpeak
      -- (slo by rovnou takto, exact hk_memP n (hk_strict n))

    -- ted uz vime, vse potrebne, tj. ze k existuje, ze je ostre rostouci a dana podposloupnost je monotonni
    exact ⟨k, k_strict_inc, h_dec⟩
  · -- v pripade konecne mnoziny P
    have hfin : P.Finite := by exact Set.not_infinite.mp hInf
    -- najdeme index N od ktereho uz neni zadny prvek P, tj. posledni Peak
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, n ∉ P := by
      -- vime, ze kazda konecna mnozina ma horni mez
      obtain ⟨B, hB⟩ : ∃ B, ∀ n ∈ P, n ≤ B := by exact Set.exists_upper_bound_image P (fun b => b) hfin
      use B + 1
      intro n hnB hnP
      have : n ≤ B := by exact hB n hnP
      have : n < B + 1 := by exact Nat.lt_succ_of_le (hB n hnP)
      exact (not_lt_of_ge hnB) this

    -- pro n vetsi nez N (posledni Peak), vzdy najdu m tak, ze hodnota posloupnosti v tomto je vetsi nez pro n, tj, a m > a n
    -- tj. vzdy najdu vetsi prvek
    have step : ∀ n ≥ N, ∃ m, n < m ∧ a n < a m := by
      intro n hn
      have : n ∉ P := by exact hN n hn
      -- z ji dokazaneho lemmatu
      simpa [not_peak_iff_exists_gt a n, P] using this

    -- opet si vezmeme next z existence
    choose next hnext using step

    -- next nam rika, ze pro kazdy index n ≥ N umime najit nejaky dalsi index s vetsi hodnotou
    -- u next ale je jeste vzdy potreba ukazat ze n ≥ N, tedy vytvorime si funkci next', kde toto neni a ukazeme ze ani byt nemusi tim ze volame next na max t N, tedy at bude t jakekoliv, vzdy bude argument funkce ≥ N
    -- next' nam vraci dalsi vetsi index nez max t N
    let next' : ℕ → ℕ := fun t => next (max t N) (le_max_right _ _)
    have next'_eq_next_of_ge {t} (ht : t ≥ N) : next' t = next t ht := by
      unfold next'
      have : max t N = t := max_eq_left ht
      simp [this]

    -- a zkonstruujeme posloupnost k
    let k : ℕ → ℕ := Nat.rec N (fun _ kn => next' kn)
    have k_zero : k 0 = N := by simp [k]
    have k_succ (n : ℕ) : k (n + 1) = next' (k n) := by simp [k]

    -- pomocne, ze k n je vzdy ≥ N
    have kn_geN : ∀ n, k n ≥ N := by
      intro n
      induction' n with i ki
      · rw [k_zero]
      · rw [k_succ]
        have : N < next' (k i) := by
          unfold next'
          have : max (k i) N < next (max (k i) N) (le_max_right _ _) := (hnext (max (k i) N) (le_max_right _ _)).1
          exact lt_of_le_of_lt (le_max_right _ _) this
        exact Nat.le_of_succ_le this

    --  k je ostre rostouci
    have k_strict_inc : StrictlyIncreasingSequenceN k := by
      intro n
      rw [k_succ]
      -- pomocne, ze k (n + 1) = next (k n)
      have : k (n+1) = next (k n) (kn_geN n) := by
        exact next'_eq_next_of_ge (kn_geN n)
      have h := (hnext (k n) (kn_geN n)).1
      exact Nat.lt_of_lt_of_eq h (id (Eq.symm this))

    -- podposloupnost je ostre rostouci
    have a_k_strict_mono : StrictlyIncreasingSequence (Subsequence a k) := by
      unfold StrictlyIncreasingSequence Subsequence
      intro n
      have h := (hnext (k n) (kn_geN n)).2
      simpa [k_succ n, next'_eq_next_of_ge (kn_geN n)] using h

    -- a pro splneni dukazu potrebuji jen ukazat je je tim padem i monotonni
    have h_inc : MonotonicSequence (Subsequence a k) := by
      unfold MonotonicSequence IncreasingSequence Subsequence
      left
      intro n
      exact le_of_lt (a_k_strict_mono n)

    exact ⟨k, k_strict_inc, h_inc⟩

-- #print axioms monoSubsequence
