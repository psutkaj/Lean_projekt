import LEANprj.defs
open Classical

-- Definujeme pojem "vrcholu" (Peak point).
private def Peak (a : ℕ → ℝ) (n : ℕ) : Prop := ∀ m : ℕ, n < m → a m ≤ a n

-- Logická negace vrcholu
lemma not_peak_iff_exists_gt (a : ℕ → ℝ) (n : ℕ) : ¬ Peak a n ↔ ∃ m > n, a n < a m := by
  unfold Peak; push_neg; rfl

-- Pomocné lemma: Pokud je množina P nekonečná, pro každé t najdeme prvek v P ostře větší než t.
lemma exists_mem_P_gt_of_infinite (P : Set ℕ) (hInf : P.Infinite) (t : ℕ) : ∃ m ∈ P, t < m := by
  by_contra! h
  exact hInf (Set.finite_Iic t |>.subset h)

-- Věta: Z každé posloupnosti v ℝ lze vybrat monotonní podposloupnost.
theorem exists_mono_subseq (a : ℕ → ℝ) :
  ∃ k : ℕ → ℕ, StrictlyIncreasingSequenceN k ∧ MonotonicSequence (Subsequence a k) := by
  let P : Set ℕ := {n | Peak a n}
  by_cases hInf : P.Infinite
  · -- PŘÍPAD 1: Množina vrcholů P je nekonečná.
    have step : ∀ t, ∃ m ∈ P, t < m := exists_mem_P_gt_of_infinite P hInf
    choose next hnext_P hnext_gt using step
    -- Zkonstruujeme indexovou posloupnost k rekurzivně.
    let k : ℕ → ℕ := fun n => Nat.rec (next 0) (fun _ kn => next kn) n
    have k_succ (n : ℕ) : k (n + 1) = next (k n) := rfl
    have k_inc : StrictlyIncreasingSequenceN k :=
    by
      intro n
      rw [k_succ]
      exact hnext_gt (k n)
    -- Ukážeme, že všechny vybrané indexy leží v P.
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
    exact k_in_P n _ (k_inc n)

  · -- PŘÍPAD 2: Množina vrcholů P je konečná.
    obtain ⟨B, hB⟩ := Set.exists_upper_bound_image P id (Set.not_infinite.mp hInf)
    -- Všechny indexy od B + 1 výše už NEJSOU vrcholy.
    have hN : ∀ n ≥ B + 1, n ∉ P := by
      intro n hn hnP
      have hle : n ≤ B := hB n hnP
      have hlt : n < B + 1 := Nat.lt_succ_of_le hle
      exact (not_lt_of_ge hn) hlt
    -- Protože n >= B+1 není vrchol, existuje index m > n s ostře větší hodnotou.
    have step : ∀ n ≥ B + 1, ∃ m > n, a n < a m := by
      intro n hn
      exact (not_peak_iff_exists_gt a n).mp (hN n hn)
    choose next hnext_gt hnext_val using step
    let next' (t : ℕ) := next (max t (B + 1)) (le_max_right _ _)
    let k : ℕ → ℕ := λ n => Nat.rec (B + 1) (λ _ kn => next' kn) n
    have k_succ (n : ℕ) : k (n + 1) = next' (k n) := rfl
    have hk_ge : ∀ n, B + 1 ≤ k n := by
      intro n;
      induction' n with d hd
      · exact le_refl _
      · exact le_trans (le_max_right _ _) (le_of_lt (hnext_gt _ _))
    -- Důkaz ostře rostoucí posloupnosti indexů.
    have k_inc : StrictlyIncreasingSequenceN k := by
      intro n
      rw [k_succ]
      have h_max : max (k n) (B + 1) = k n := max_eq_left (hk_ge n)
      exact
        lt_of_eq_of_lt (id (Eq.symm h_max))
          (hnext_gt (max (k n) (B + 1)) (le_max_right (k n) (B + 1)))
    -- Důkaz monotonie.
    have h_mono : MonotonicSequence (Subsequence a k) := by
      left; intro n; dsimp [Subsequence, IncreasingSequence]
      have h_max : max (k n) (B + 1) = k n := max_eq_left (hk_ge n)
      have h_val := hnext_val (max (k n) (B + 1)) (le_max_right _ _)
      rw [k_succ]; dsimp [next']
      have h_a_eq : a (max (k n) (B + 1)) = a (k n) := by rw [h_max]
      rw [h_a_eq] at h_val
      exact le_of_lt h_val
    exact ⟨k, k_inc, h_mono⟩
