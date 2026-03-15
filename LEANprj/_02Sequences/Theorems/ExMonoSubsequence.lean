import LEANprj.defs
open Classical

-- Definujeme pojem "vrcholu" (Peak point).
-- private znamená, že tuto definici nebudeme exportovat mimo tento soubor.
private def Peak (a : ℕ → ℝ) (n : ℕ) : Prop := ∀ {m : ℕ}, n < m → a m ≤ a n

-- Logická negace vrcholu. Taktika push_neg zde elegantně aplikuje De Morganova pravidla.
lemma not_peak_iff_exists_gt (a : ℕ → ℝ) (n : ℕ) : ¬ Peak a n ↔ ∃ m > n, a n < a m := by
  unfold Peak; push_neg; rfl

-- Pomocné lemma: Pokud je množina P nekonečná, pro každé t najdeme prvek v P ostře větší než t.
lemma exists_mem_P_gt_of_infinite (P : Set ℕ) (hInf : P.Infinite) (t : ℕ) : ∃ m ∈ P, t < m := by
  by_contra h;
  push_neg at h
  have hsub : P ⊆ Set.Iic t := fun m hmP => h m hmP
  exact hInf (Set.finite_Iic t |>.subset hsub)

-- Věta: Z každé posloupnosti v ℝ lze vybrat monotonní podposloupnost.
theorem ExMonoSubsequence (a : ℕ → ℝ) :
  ∃ k : ℕ → ℕ, StrictlyIncreasingSequenceN k ∧ MonotonicSequence (Subsequence a k) := by

  -- Zavedeme množinu všech vrcholů posloupnosti.
  let P : Set ℕ := {n | Peak a n}

  -- Rozdělíme důkaz na dva klasické případy.
  by_cases hInf : P.Infinite

  · -- ==========================================
    -- PŘÍPAD 1: Množina vrcholů P je nekonečná.
    -- ==========================================
    have step : ∀ t, ∃ m ∈ P, t < m := exists_mem_P_gt_of_infinite P hInf

    -- Axiom závislého výběru: Z existence vyrobíme konkrétní funkci 'next'.
    choose next hnext_P hnext_gt using step

    -- Zkonstruujeme indexovou posloupnost k rekurzivně.
    let k : ℕ → ℕ := fun n => Nat.rec (next 0) (fun _ kn => next kn) n
    have k_succ (n : ℕ) : k (n + 1) = next (k n) := rfl

    -- Ukážeme, že k je ostře rostoucí.
    have k_inc : StrictlyIncreasingSequenceN k :=
    by
      intro n
      rw [k_succ]
      exact hnext_gt (k n)

    -- Ukážeme, že všechny vybrané indexy leží v P (jsou to vrcholy).
    have k_in_P : ∀ n, k n ∈ P := by
      intro n
      induction' n with d hd
      · exact hnext_P 0
      · rw [k_succ]
        exact hnext_P (k d)

    use k, k_inc
    -- Dokážeme monotonii: Protože skáčeme jen po vrcholech, posloupnost klesá.
    right
    intro n
    exact k_in_P n (k_inc n)

  · -- ==========================================
    -- PŘÍPAD 2: Množina vrcholů P je konečná.
    -- ==========================================
    -- Najdeme horní závoru B pro množinu P.
    obtain ⟨B, hB⟩ := Set.exists_upper_bound_image P id (Set.not_infinite.mp hInf)

    -- Všechny indexy od B + 1 výše už NEJSOU vrcholy.
    have hN : ∀ n ≥ B + 1, n ∉ P := fun n hn hnP => by
      have hle : n ≤ B := hB n hnP
      have hlt : n < B + 1 := Nat.lt_succ_of_le hle
      exact (not_lt_of_ge hn) hlt

    -- Protože n >= B+1 není vrchol, existuje index m > n s ostře větší hodnotou.
    have step : ∀ n ≥ B + 1, ∃ m > n, a n < a m := fun n hn =>
      (not_peak_iff_exists_gt a n).mp (hN n hn)
    choose next hnext_gt hnext_val using step

    -- TRIK PRO OBEJITÍ ZÁVISLÝCH TYPŮ:
    -- Funkce 'next' vyžaduje důkaz hn : n >= B + 1. Abychom mohli použít obyčejnou rekurzi,
    -- zavádíme 'next'', které samo zajišťuje podmínku pomocí funkce max.
    let next' (t : ℕ) := next (max t (B + 1)) (le_max_right _ _)

    let k : ℕ → ℕ := fun n => Nat.rec (B + 1) (fun _ kn => next' kn) n
    have k_succ (n : ℕ) : k (n + 1) = next' (k n) := rfl

    -- Pomocné lemma: Naše vybrané indexy k_n vždy přesáhnou hranici B + 1.
    have hk_ge : ∀ n, B + 1 ≤ k n := by
      intro n; induction n with
      | zero => exact le_refl _
      | succ i ih => exact le_trans (le_max_right _ _) (le_of_lt (hnext_gt _ _))

    -- Důkaz ostře rostoucí posloupnosti indexů.
    have k_inc : StrictlyIncreasingSequenceN k := fun n => by
      rw [k_succ]
      -- Pro max(k_n, B+1) platí, že je to přímo k_n, protože k_n >= B+1.
      have h_max : max (k n) (B + 1) = k n := max_eq_left (hk_ge n)
      have h_lt := hnext_gt (max (k n) (B + 1)) (le_max_right _ _)
      -- Přepíšeme max na k_n na levé straně nerovnosti.
      rw [←h_max] at h_lt
      exact
        lt_of_eq_of_lt (id (Eq.symm h_max))
          (hnext_gt (max (k n) (B + 1)) (le_max_right (k n) (B + 1)))

    -- Důkaz monotonie (zde ostře rostoucí posloupnosti hodnot).
    have h_mono : MonotonicSequence (Subsequence a k) := by
      left; intro n; dsimp [Subsequence, IncreasingSequence]
      have h_max : max (k n) (B + 1) = k n := max_eq_left (hk_ge n)
      -- Hodnota naší posloupnosti skutečně roste podle vlastnosti hnext_val.
      have h_val := hnext_val (max (k n) (B + 1)) (le_max_right _ _)
      rw [k_succ]; dsimp [next']
      -- Pomocí přepsání max na k_n dostáváme čistý cíl.
      have h_a_eq : a (max (k n) (B + 1)) = a (k n) := by rw [h_max]
      rw [h_a_eq] at h_val
      exact le_of_lt h_val

    exact ⟨k, k_inc, h_mono⟩


-- private def Peak (a : ℕ → ℝ) (n : ℕ) : Prop := ∀ {m : ℕ}, n < m → a m ≤ a n

-- lemma peak_iff (a : ℕ → ℝ) (n : ℕ) : Peak a n ↔ ∀ m > n, a m ≤ a n := by
--   rfl

-- lemma not_peak_iff_exists_gt (a : ℕ → ℝ) (n : ℕ) : ¬ Peak a n ↔ ∃ m, n < m ∧ a n < a m := by
--   unfold Peak
--   push_neg
--   rfl

-- -- z nekonecnosti P ∀ t ∈ P ∃ m ∈ P : t < m, tj. vzdy ∃ m ∈ P vetsi nez t
-- lemma exists_mem_P_gt_of_infinite (P : Set ℕ) (hInf : P.Infinite) (t : ℕ) : ∃ m, m ∈ P ∧ t < m := by
--   -- kdyby neexistovalo m > t v P, pak P by byla omezena tim t, a tedy P je konecna — spor.
--   by_contra h
--   push_neg at h   -- h : ∀ m ∈ P : m ≤ t
--   -- P ⊆ (-∞, t⟩
--   have hsub : P ⊆ Set.Iic t := by
--     intro m hmP
--     exact h m hmP
--   -- podmnozina ℕ omezena prvkem t je konecna
--   have hfin_Iic : (Set.Iic t : Set ℕ).Finite := by exact Set.finite_Iic t
--   -- a tedy P je konecna
--   have hfinP : P.Finite := hfin_Iic.subset hsub
--   -- coz je spor
--   exact hInf hfinP


-- -- Věta: Z každé posloupnosti v ℝ lze vybrat monotonní podposloupnost.
-- theorem ExMonoSubsequence : ∀ (a : ℕ → ℝ), ∃ k : ℕ → ℕ, StrictlyIncreasingSequenceN k ∧ MonotonicSequence (Subsequence a k) := by
--   intro a
--   -- zavedeme mnozinu Peaks
--   let P : Set ℕ := {n | Peak a n}

--   -- a mame dva pripady, bud je P nekonecna nebo ne
--   by_cases hInf : P.Infinite
--   · -- pro pripad, ze P je nekonecna, tj mam nekonecne mnoho Peak pointu, tak si vzdy do podposloupnosti volim prave tyto body
--     -- z definice peak pointu je tato posloupnost kleasiji a tedy monotonni

--     -- vybereme si svedka k : ℕ → ℕ, ostre rostouciho a k ⊆ P
--     obtain ⟨k, k_strict_inc, k_in_P⟩ : ∃ k : ℕ → ℕ, StrictlyIncreasingSequenceN k ∧ ∀ n, k n ∈ P := by
--       -- vzdy mame dalsi krok
--       have step : ∀ t : ℕ, ∃ m, m ∈ P ∧ t < m := by
--         intro t
--         -- coz uz mame dokazane z nekonecnosti P
--         exact exists_mem_P_gt_of_infinite P hInf t

--       -- vezmeme si funkci nalsedovnika t
--       choose next hnext_mem hnext_gt using step

--       -- zkonstruujeme k : ℕ → ℕ rekurzivne pomoci next
--       let k : ℕ → ℕ := Nat.rec (next 0) (fun n kn => next kn)
--       have k_zero : k 0 = next 0 := by simp [k]
--       have k_succ (n) : k (n+1) = next (k n) := by simp [k]

--       -- a ukazeme ze je ostre rostouci
--       have k_strict_inc : StrictlyIncreasingSequenceN k := by
--         unfold StrictlyIncreasingSequenceN
--         intro n
--         simpa [k_succ n] using hnext_gt (k n)

--       -- a ze je podmnozinou P
--       have k_in_P : ∀ n, k n ∈ P := by
--         intro n
--         induction' n with i ih
--         · rw [k_zero]
--           exact hnext_mem 0
--         · rw [k_succ]
--           exact hnext_mem (k i)
--       exact ⟨k, k_strict_inc, k_in_P⟩

--     -- ted tedy mam uz vyrobenou k : ℕ → ℕ ostre rostouci a kazdy prvek je Peakpoint
--     -- potrebuji jeste ukazat je podposloupnost s nasi k je klesajici
--     have h_dec : MonotonicSequence (Subsequence a k) := by
--       unfold MonotonicSequence
--       right
--       unfold DecreasingSequence Subsequence
--       intro n
--       -- vime, ze kazdy clen podposloupnosti je Peak
--       have hpeak : Peak a (k n) := by exact k_in_P n
--       unfold Peak at hpeak
--       -- potrebujeme pro dalsi krok jen ukazat toto
--       have k_inc : k n < k (n + 1) := by exact k_strict_inc n
--       -- a do hpeak dosadime za m = n + 1
--       specialize hpeak k_inc
--       exact hpeak
--       -- (slo by rovnou takto, exact hk_memP n (hk_strict n))

--     -- ted uz vime, vse potrebne, tj. ze k existuje, ze je ostre rostouci a dana podposloupnost je monotonni
--     exact ⟨k, k_strict_inc, h_dec⟩
--   · -- v pripade konecne mnoziny P
--     have hfin : P.Finite := by exact Set.not_infinite.mp hInf
--     -- najdeme index N od ktereho uz neni zadny prvek P, tj. posledni Peak
--     obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, n ∉ P := by
--       -- vime, ze kazda konecna mnozina ma horni mez
--       obtain ⟨B, hB⟩ : ∃ B, ∀ n ∈ P, n ≤ B := by exact Set.exists_upper_bound_image P (fun b => b) hfin
--       use B + 1
--       intro n hnB hnP
--       have : n ≤ B := by exact hB n hnP
--       have : n < B + 1 := by exact Nat.lt_succ_of_le (hB n hnP)
--       exact (not_lt_of_ge hnB) this

--     -- pro n vetsi nez N (posledni Peak), vzdy najdu m tak, ze hodnota posloupnosti v tomto je vetsi nez pro n, tj, a m > a n
--     -- tj. vzdy najdu vetsi prvek
--     have step : ∀ n ≥ N, ∃ m, n < m ∧ a n < a m := by
--       intro n hn
--       have : n ∉ P := by exact hN n hn
--       -- z ji dokazaneho lemmatu
--       simpa [not_peak_iff_exists_gt a n, P] using this

--     -- opet si vezmeme next z existence
--     choose next hnext using step

--     -- next nam rika, ze pro kazdy index n ≥ N umime najit nejaky dalsi index s vetsi hodnotou
--     -- u next ale je jeste vzdy potreba ukazat ze n ≥ N, tedy vytvorime si funkci next', kde toto neni a ukazeme ze ani byt nemusi tim ze volame next na max t N, tedy at bude t jakekoliv, vzdy bude argument funkce ≥ N
--     -- next' nam vraci dalsi vetsi index nez max t N
--     let next' : ℕ → ℕ := fun t => next (max t N) (le_max_right _ _)
--     have next'_eq_next_of_ge {t} (ht : t ≥ N) : next' t = next t ht := by
--       unfold next'
--       have : max t N = t := max_eq_left ht
--       simp [this]

--     -- a zkonstruujeme posloupnost k
--     let k : ℕ → ℕ := Nat.rec N (fun _ kn => next' kn)
--     have k_zero : k 0 = N := by simp [k]
--     have k_succ (n : ℕ) : k (n + 1) = next' (k n) := by simp [k]

--     -- pomocne, ze k n je vzdy ≥ N
--     have kn_geN : ∀ n, k n ≥ N := by
--       intro n
--       induction' n with i ki
--       · rw [k_zero]
--       · rw [k_succ]
--         have : N < next' (k i) := by
--           unfold next'
--           have : max (k i) N < next (max (k i) N) (le_max_right _ _) := (hnext (max (k i) N) (le_max_right _ _)).1
--           exact lt_of_le_of_lt (le_max_right _ _) this
--         exact Nat.le_of_succ_le this

--     --  k je ostre rostouci
--     have k_strict_inc : StrictlyIncreasingSequenceN k := by
--       intro n
--       rw [k_succ]
--       -- pomocne, ze k (n + 1) = next (k n)
--       have : k (n+1) = next (k n) (kn_geN n) := by
--         exact next'_eq_next_of_ge (kn_geN n)
--       have h := (hnext (k n) (kn_geN n)).1
--       exact Nat.lt_of_lt_of_eq h (id (Eq.symm this))

--     -- podposloupnost je ostre rostouci
--     have a_k_strict_mono : StrictlyIncreasingSequence (Subsequence a k) := by
--       unfold StrictlyIncreasingSequence Subsequence
--       intro n
--       have h := (hnext (k n) (kn_geN n)).2
--       simpa [k_succ n, next'_eq_next_of_ge (kn_geN n)] using h

--     -- a pro splneni dukazu potrebuji jen ukazat je je tim padem i monotonni
--     have h_inc : MonotonicSequence (Subsequence a k) := by
--       unfold MonotonicSequence IncreasingSequence Subsequence
--       left
--       intro n
--       exact le_of_lt (a_k_strict_mono n)

--     exact ⟨k, k_strict_inc, h_inc⟩

-- -- #print axioms ExMonoSubsequence

-- theorem ExMonoSubsequence' :
--     ∀ (a : ℕ → ℝ),
--       ∃ k : ℕ → ℕ, StrictlyIncreasingSequenceN k ∧ MonotonicSequence (Subsequence a k) :=
-- by
--   classical
--   intro a

--   -- Peaks: indices n such that all later values are ≤ a n
--   let P : Set ℕ := {n : ℕ | ∀ m : ℕ, n < m → a m ≤ a n}

--   --------------------------------------------------------------------
--   -- Lemma: infinite P ⊆ ℕ ⇒ ∃ k strictly increasing with k n ∈ P
--   -- (this one is nondependent, because step doesn't need an invariant)
--   --------------------------------------------------------------------
--   have infinite_nat_has_strictInc_seq :
--       ∀ P : Set ℕ, Set.Infinite P →
--         ∃ k : ℕ → ℕ, StrictlyIncreasingSequenceN k ∧ ∀ n : ℕ, k n ∈ P := by
--     intro P hPinf

--     have h_unbdd : ¬ BddAbove P := by
--       intro hbdd
--       rcases hbdd with ⟨B, hB⟩
--       have hsub : P ⊆ Set.Icc (0 : ℕ) B := by
--         intro n hn
--         exact ⟨Nat.zero_le n, hB hn⟩
--       have hfinIcc : Set.Finite (Set.Icc (0 : ℕ) B) := by
--         simpa using (Set.finite_Icc (0 : ℕ) B)
--       have hfinP : Set.Finite P := hfinIcc.subset hsub
--       exact hPinf hfinP

--     have step : ∀ N : ℕ, ∃ n : ℕ, n ∈ P ∧ N < n := by
--       intro N
--       by_contra hcontra
--       have hbdd : BddAbove P := by
--         refine ⟨N, ?_⟩
--         intro n hn
--         by_contra hnot
--         have hnlt : N < n := Nat.lt_of_not_ge hnot
--         exact hcontra ⟨n, hn, hnlt⟩
--       exact h_unbdd hbdd

--     let k : ℕ → ℕ :=
--       Nat.rec (Classical.choose (step 0))
--         (fun _ kn => Classical.choose (step kn))

--     have hk_mem : ∀ n : ℕ, k n ∈ P := by
--       intro n
--       induction n with
--       | zero =>
--           simpa [k] using (Classical.choose_spec (step 0)).1
--       | succ n ih =>
--           have : k (n + 1) = Classical.choose (step (k n)) := by
--             simp [k, Nat.rec, Nat.succ_eq_add_one]
--           simpa [this] using (Classical.choose_spec (step (k n))).1

--     have hk_strict : StrictlyIncreasingSequenceN k := by
--       intro n
--       have hlt : k n < Classical.choose (step (k n)) :=
--         (Classical.choose_spec (step (k n))).2
--       have : k (n + 1) = Classical.choose (step (k n)) := by
--         simp [k, Nat.rec, Nat.succ_eq_add_one]
--       simpa [this] using hlt

--     exact ⟨k, hk_strict, hk_mem⟩

--   --------------------------------------------------------------------
--   -- Main proof split on P infinite/finite
--   --------------------------------------------------------------------
--   by_cases hPinf : Set.Infinite P
--   · -- Infinite peaks ⇒ decreasing subsequence
--     rcases infinite_nat_has_strictInc_seq P hPinf with ⟨k, hk_strict, hkP⟩
--     refine ⟨k, hk_strict, Or.inr ?_⟩
--     intro n
--     have hkPn : k n ∈ P := hkP n
--     have hknlt : k n < k (n + 1) := hk_strict n
--     have : a (k (n + 1)) ≤ a (k n) := hkPn (k (n + 1)) hknlt
--     simpa [Subsequence, Function.comp] using this

--   · -- Finite peaks ⇒ build increasing subsequence with dependent recursion
--     have hPfin : Set.Finite P := Set.not_infinite.mp hPinf
--     rcases hPfin.bddAbove with ⟨B, hB⟩
--     let N : ℕ := B + 1

--     have hN_not_peak : ∀ n : ℕ, n ≥ N → n ∉ P := by
--       intro n hn hnP
--       have hnle : n ≤ B := hB hnP
--       have : n < B + 1 := Nat.lt_succ_of_le hnle
--       exact (Nat.not_lt_of_ge hn) this

--     have step_ex : ∀ n : ℕ, n ≥ N → ∃ m : ℕ, n < m ∧ a n < a m := by
--       intro n hn
--       have hnP : n ∉ P := hN_not_peak n hn
--       have : ∃ m : ℕ, n < m ∧ ¬ (a m ≤ a n) := by
--         simpa [P] using hnP
--       rcases this with ⟨m, hnm, hnotle⟩
--       exact ⟨m, hnm, lt_of_not_ge hnotle⟩

--     -- Dependent recursion carrying invariant N ≤ k n:
--     let F : ℕ → {t : ℕ // N ≤ t} :=
--       Nat.rec ⟨N, le_rfl⟩ (fun _ prev =>
--         let kn : ℕ := prev.1
--         let hkn : N ≤ kn := prev.2
--         let m : ℕ := Classical.choose (step_ex kn hkn)
--         have hkm : kn < m := (Classical.choose_spec (step_ex kn hkn)).1
--         have hNm : N ≤ m := le_trans hkn (Nat.le_of_lt hkm)
--         ⟨m, hNm⟩)

--     let k : ℕ → ℕ := fun n => (F n).1

--     have hk_step :
--         ∀ n : ℕ, k n < k (n + 1) ∧ a (k n) < a (k (n + 1)) := by
--       intro n
--       -- unfold one step of F at succ
--       -- F (n+1) is built using choose (step_ex (k n) (F n).2)
--       have hFn : F n = ⟨k n, (F n).2⟩ := by
--         rfl
--       -- compute F (n+1) by simp
--       -- easiest: just unfold k,F and use Nat.rec equations
--       -- We do it by rewriting k (n+1) to the chosen m
--       have hk_succ :
--           k (n + 1) =
--             Classical.choose (step_ex (k n) (F n).2) := by
--         -- simp knows Nat.rec at succ
--         simp [k, F, Nat.rec, Nat.succ_eq_add_one]
--       have hspec := Classical.choose_spec (step_ex (k n) (F n).2)
--       refine ⟨?_, ?_⟩
--       · -- k n < k (n+1)
--         simpa [hk_succ] using hspec.1
--       · -- a (k n) < a (k (n+1))
--         simpa [hk_succ] using hspec.2

--     have hk_strict : StrictlyIncreasingSequenceN k := by
--       intro n
--       exact (hk_step n).1

--     have h_incr : IncreasingSequence (Subsequence a k) := by
--       intro n
--       have : a (k n) < a (k (n + 1)) := (hk_step n).2
--       simpa [Subsequence, Function.comp] using (le_of_lt this)

--     exact ⟨k, hk_strict, Or.inl h_incr⟩



-- -- #print axioms ExMonoSubsequence
