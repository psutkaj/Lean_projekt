import LEANprj.Sequences.definitions
noncomputable section
open Classical

variable (A : Set ℝ) (l₀ u₀ : ℝ) (n : ℕ)

-- zavedu jako axiom, z uplnosti Realnych cisel
axiom exists_point_in_nested_intervals
  (l u : ℕ → ℝ)
  (inc_l : IncreasingSequence l)
  (dec_u : DecreasingSequence u)
  (sep : ∀ n, l n ≤ u n)
  (shrink : ∀ n, u (n+1) - l (n+1) = (u n - l n) / 2) :
  ∃ s : ℝ, ∀ n, l n ≤ s ∧ s ≤ u n

-- chci si vytvorit puleni intervalu, a aby ho rozeznavalo simp
@[simp] def mid (l u : ℝ) : ℝ := (l + u) / 2

-- lemmata o delce intervalu po puleni
lemma sub_mid (l u : ℝ) : u - mid l u = (u - l) / 2 := by simp; ring
lemma mid_sub (l u : ℝ) : mid l u - l = (u - l) / 2 := by simp; ring

-- definuju krok puleni, beru bud levou nebo pravou cast, podle toho kde mam a ∈ A
def step (l u : ℝ) : ℝ × ℝ := if _ : ∃ a : A, mid l u < a then (mid l u, u) else (l, mid l u)

-- definuju si posloupnost dvojic (lₙ, uₙ)
def luNext : ℕ → ℝ × ℝ
  | 0 => (l₀, u₀)
  | n+1 => step A (luNext n).1 (luNext n).2

-- zadefinuju si posloupnosti pro samostatne lₙ, uₙ
def lSeq (n : ℕ) : ℝ := (luNext A l₀ u₀ n).1
def uSeq (n : ℕ) : ℝ := (luNext A l₀ u₀ n).2

-- lemmata pro porovnani prvku s pulenim
lemma left_le_mid {l u : ℝ} (h : l ≤ u) : l ≤ mid l u := by
  unfold mid
  have : l = (l + l) / 2 := by ring
  have : l + l ≤ l + u := by linarith
  linarith

lemma mid_le_right {l u : ℝ} (h : l ≤ u) : mid l u ≤ u := by
  unfold mid
  have : (u + u) / 2 = u := by ring
  have : u + l ≤ u + u := by linarith
  linarith

-- exsitence a jednoznacnost suprema
-- kazda neprazdna, shora omezena mnozina ma prave jedno supremum
theorem exists_unique_supremum (A : Set ℝ) (hA : A.Nonempty) (hUpperBdd : ∃ u : ℝ, ∀ a ∈ A, a ≤ u): ∃! s : ℝ, IsSup A s := by
  -- z nonempty A si vytahnu l₀ () a hl₀
  obtain ⟨l₀, hl₀⟩ := hA
  -- z horni omezenosti si vytahnu u₀ () a hl₀
  obtain ⟨u₀, hu₀⟩ := hUpperBdd
  -- vime, ze l₀ ≤ u₀
  have h_l₀_leq_u₀ : l₀ ≤ u₀ := by exact hu₀ l₀ hl₀

  -- ukazeme, ze ∀ n ∈ ℕ : lₙ ≤ uₙ
  have lₙ_leq_uₙ : ∀ n : ℕ, lSeq A l₀ u₀ n ≤ uSeq A l₀ u₀ n := by
    intro n
    induction' n with d hd
    · simp [lSeq, uSeq, luNext]
      exact h_l₀_leq_u₀
    · simp [lSeq, uSeq, luNext]
      let l_d := lSeq A l₀ u₀ d
      let u_d := uSeq A l₀ u₀ d
      let lu_d_next := step A l_d u_d
      change lu_d_next.1 ≤ lu_d_next.2
      unfold lu_d_next step mid
      simp_all only [Subtype.exists, exists_prop, dite_eq_ite, l_d, u_d]
      split
      next h =>
        simp_all only
        obtain ⟨w, h⟩ := h
        obtain ⟨left, right⟩ := h
        linarith
      next h =>
        simp_all only [not_exists, not_and, not_lt]
        linarith

  -- horni zavora
  have upperBound : ∀ n : ℕ, ∀ a ∈ A, a ≤ uSeq A l₀ u₀ n := by
    intro n a ha
    induction' n with d hd
    · unfold uSeq luNext
      simp
      exact hu₀ a ha
    · unfold uSeq luNext step
      simp only [Subtype.exists, exists_prop, dite_eq_ite]
      split_ifs with h
      · exact hd
      · push_neg at h
        exact h a ha

  -- do sebe vlozene intervaly neprazdne
  have nestedNonempty : ∀ n : ℕ, ∃ a ∈ A, lSeq A l₀ u₀ n ≤ a ∧ a ≤ uSeq A l₀ u₀ n := by
    intro n
    induction' n with d hd
    · use l₀
      constructor
      · exact hl₀
      · constructor
        · simp [lSeq, luNext]
        · simp [uSeq, luNext]
          exact hu₀ l₀ hl₀
    · obtain ⟨a, ha, ha_l, ha_u⟩ := hd
      unfold lSeq uSeq luNext step
      simp only [Subtype.exists, exists_prop, dite_eq_ite]
      split_ifs with h
      · obtain ⟨w, hw_mem, hw_gt⟩ := h
        use w
        refine ⟨hw_mem, ?_, upperBound d w hw_mem⟩
        show mid (luNext A l₀ u₀ d).1 (luNext A l₀ u₀ d).2 ≤ w
        have : lSeq A l₀ u₀ d = (luNext A l₀ u₀ d).1 := rfl
        have : uSeq A l₀ u₀ d = (luNext A l₀ u₀ d).2 := rfl
        exact le_of_lt hw_gt
      · push_neg at h
        use a
        refine ⟨ha, ha_l, ?_⟩
        show a ≤ mid (lSeq A l₀ u₀ d) (uSeq A l₀ u₀ d)
        exact h a ha

  -- puleni intervalu
  have shrink : ∀ n : ℕ, uSeq A l₀ u₀ (n+1) - lSeq A l₀ u₀ (n+1) = (uSeq A l₀ u₀ n - lSeq A l₀ u₀ n) / 2 := by
    intro n
    set l := lSeq A l₀ u₀ n with hl
    set u := uSeq A l₀ u₀ n with hu
    have : lSeq A l₀ u₀ n = (luNext A l₀ u₀ n).1 := rfl
    have : uSeq A l₀ u₀ n = (luNext A l₀ u₀ n).2 := rfl
    by_cases hRight : ∃ a : A, mid l u < a
    · have h_l_succ : lSeq A l₀ u₀ (n+1) = mid l u := by
        simp [lSeq, luNext, step]
        split_ifs with h
        · simp
          rw [hl, hu]
          unfold lSeq uSeq
          ring
        · simp
          rw [hl, hu]
          unfold lSeq uSeq
          simp_all only [mid, Subtype.exists, exists_prop, l, u]
      have h_u_succ : uSeq A l₀ u₀ (n+1) = u := by
        simp [uSeq, luNext, step]
        split_ifs with h
        · simp
          exact hu
        · simp
          rw [hu]
          unfold uSeq
          simp_all only [mid, Subtype.exists, exists_prop, l, u]
      calc
        uSeq A l₀ u₀ (n+1) - lSeq A l₀ u₀ (n+1) = u - mid l u := by simp_all only [mid, Subtype.exists, exists_prop, l, u]
        _ = (u - l) / 2 := by exact sub_mid l u
    · have h_l_succ : lSeq A l₀ u₀ (n+1) = l := by
        simp [lSeq, luNext, step]
        split_ifs with h
        · simp
          rw [hl]
          unfold lSeq
          simp_all only [mid, Subtype.exists, exists_prop, not_true_eq_false, l, u]
        · simp
          rw [hl]
          unfold lSeq
          exact hl
      have h_u_succ : uSeq A l₀ u₀ (n+1) = mid l u := by
        simp [uSeq, luNext, step]
        split_ifs with h
        · simp
          rw [hl, hu]
          unfold lSeq uSeq
          simp_all only [mid, Subtype.exists, exists_prop, not_true_eq_false, l, u]
        · simp
          rw [hu]
          unfold uSeq
          exact rfl
      calc
        uSeq A l₀ u₀ (n + 1) - lSeq A l₀ u₀ (n + 1) = mid l u - l := by simp_all only [mid, Subtype.exists, exists_prop, not_exists, not_and, not_lt, l, u]
        _ = (u - l) / 2 := by exact mid_sub l u

  -- lₙ rostouci posloupnost
  have lInc : IncreasingSequence (lSeq A l₀ u₀) := by
    unfold IncreasingSequence
    intro n
    set l := lSeq A l₀ u₀ n with hl
    set u := uSeq A l₀ u₀ n with hu
    have : lSeq A l₀ u₀ n = (luNext A l₀ u₀ n).1 := rfl
    have : uSeq A l₀ u₀ n = (luNext A l₀ u₀ n).2 := rfl
    by_cases hRight : ∃ a : A, mid l u < a
    · have h_l_succ : lSeq A l₀ u₀ (n+1) = mid l u := by
        simp [lSeq, luNext, step]
        split_ifs with h
        · simp
          rw [hl, hu]
          unfold lSeq uSeq
          ring
        · simp
          rw [hl, hu]
          unfold lSeq uSeq
          simp_all only [mid, Subtype.exists, exists_prop, l, u]
      rw [h_l_succ]
      exact left_le_mid (lₙ_leq_uₙ n)
    · have h_l_succ : lSeq A l₀ u₀ (n+1) = l := by
        simp [lSeq, luNext, step]
        split_ifs with h
        · simp
          rw [hl]
          unfold lSeq
          simp_all only [mid, Subtype.exists, exists_prop, not_true_eq_false, l, u]
        · simp
          rw [hl]
          unfold lSeq
          exact hl
      rw [h_l_succ]

  -- uₙ klesajici posloupnost
  have uDec : DecreasingSequence (uSeq A l₀ u₀) := by
    unfold DecreasingSequence
    intro n
    set l := lSeq A l₀ u₀ n with hl
    set u := uSeq A l₀ u₀ n with hu
    have : lSeq A l₀ u₀ n = (luNext A l₀ u₀ n).1 := rfl
    have : uSeq A l₀ u₀ n = (luNext A l₀ u₀ n).2 := rfl
    by_cases hRight : ∃  a : A, mid l u < a
    · have h_u_succ : uSeq A l₀ u₀ (n+1) = u := by
        simp [uSeq, luNext, step]
        split_ifs with h
        · simp
          exact hu
        · simp
          rw [hu]
          unfold uSeq
          simp_all only [mid, Subtype.exists, exists_prop, l, u]
      rw [h_u_succ]
    · have h_u_succ : uSeq A l₀ u₀ (n+1) = mid l u := by
        simp [uSeq, luNext, step]
        split_ifs with h
        · simp
          rw [hl, hu]
          unfold lSeq uSeq
          simp_all only [mid, Subtype.exists, exists_prop, not_true_eq_false, l, u]
        · simp
          rw [hu]
          unfold uSeq
          exact rfl
      rw [h_u_succ]
      exact mid_le_right (lₙ_leq_uₙ n)

  -- v kazdem kroce je rozdil libovolnych dvou prvku z intervalu (lₙ, uₙ) v absolutni hodnote mensi nebo roven uₙ - lₙ (gap)
  have abs_le_gap (s t : ℝ) (hs : ∀ n, lSeq A l₀ u₀ n ≤ s ∧ s ≤ uSeq A l₀ u₀ n) (ht : ∀ n, lSeq A l₀ u₀ n ≤ t ∧ t ≤ uSeq A l₀ u₀ n) : ∀ n : ℕ, |s - t| ≤ uSeq A l₀ u₀ n - lSeq A l₀ u₀ n := by
    intro n
    set l := lSeq A l₀ u₀ n with hl
    set u := uSeq A l₀ u₀ n with hu
    have l_leq_s : l ≤ s := (hs n).1
    have s_leq_u : s ≤ u := (hs n).2
    have l_leq_t : l ≤ t := (ht n).1
    have t_leq_u : t ≤ u := (ht n).2
    exact abs_sub_le_of_le_of_le l_leq_s s_leq_u l_leq_t t_leq_u

  -- mezera (gap) se zmensuje / 2ⁿ
  have gap_shrink : ∀ n : ℕ, uSeq A l₀ u₀ n - lSeq A l₀ u₀ n = (u₀ - l₀) / 2^n := by
    intro n
    induction' n with d hd
    · simp
      rfl
    · simp_all
      ring

  -- mezera inervalu jde s rostoucim n k nule
  have gap_to_0  : ∀ ε > 0, ∃ n₀, ∀ n > n₀, |((u₀ - l₀) / 2^n)| < ε := by
    intros ε ε_pos
    have h_pos : u₀ - l₀ ≥ 0 := by linarith
    have h_abs : ∀ n, |(u₀ - l₀) / 2^n| = (u₀ - l₀) / 2^n := by
      intro n
      simp [div_nonneg h_pos]
    by_cases hGap : u₀ - l₀ = 0
    · refine ⟨0, ?_⟩
      intros n n_pos
      rw [hGap]
      simp
      linarith
    · have gap_pos : u₀ - l₀ > 0 := by exact lt_of_le_of_ne h_pos fun a => hGap (id (Eq.symm a))
      have x_pos : (u₀ - l₀) / ε > 0 := by exact div_pos gap_pos ε_pos
      have nat_le_pow_two : ∀ N : ℕ, (N : ℝ) ≤ 2 ^ N := by
        intro N
        induction' N with k ih
        · simp
        · have : (k : ℝ) ≤ 2 ^ k := ih
          have one_le : (1 : ℝ) ≤ 2 ^ k := by
            have : (0 : ℝ) < 2 := by norm_num
            have : (1 : ℝ) ≤ 2 ^ k := by refine one_le_pow₀ ?_; linarith
            exact this
          have : (k : ℝ) + 1 ≤ 2^ k + 2 ^ k := add_le_add ih one_le
          -- 2 * (2^k) = (2^k) + (2^k)
          have : 2 ^ k + 2 ^ k = 2 * 2 ^ k := by ring
          calc (↑k.succ : ℝ) = (k : ℝ) + 1 := by simp [Nat.succ_eq_add_one]
            _ ≤ 2 ^ k + 2 ^ k := add_le_add ih one_le
            _ = 2 * 2 ^ k := by ring
            _ = 2 ^ k.succ := by exact Eq.symm (pow_succ' 2 k)
      obtain ⟨N, hN⟩ := exists_nat_gt ((u₀ - l₀) / ε)
      have pow_gt :  (u₀ - l₀) / ε < 2 ^ N := by exact lt_of_le_of_lt' (nat_le_pow_two N) hN
      have posPow : 0 < (2 : ℝ) ^ N := pow_pos (by norm_num) N
      have posRight : 0 < ε / 2 ^ N := div_pos ε_pos posPow
      have step :
       ((u₀ - l₀) / ε) * (ε / 2 ^ N) < 2 ^ N * (ε / 2 ^ N) := mul_lt_mul_of_pos_right pow_gt posRight
      have base : (u₀ - l₀) / 2^N < ε := by
        calc
          (u₀ - l₀) / 2^N = (u₀ - l₀) / 2^N * ε / ε := by field_simp
          _ = ((u₀ - l₀) / ε) * (ε / (2^N)) := by ring
          _ < (2 ^ N) * (ε / (2^N)) := by exact step
          _ = ε := by field_simp
      refine ⟨N, ?_⟩
      intros n hn
      have pow_mono : 2 ^ N < 2 ^ n := by exact Nat.pow_lt_pow_right (by linarith) (by linarith)
      have posPowN : 0 < (2 : ℝ) ^ N := pow_pos (by norm_num) N
      have posPown : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
      have inv_mono : (1 : ℝ) / (2 : ℝ) ^ n < (1 : ℝ) / (2 : ℝ) ^ N := by exact div_lt_div_of_pos_left (by norm_num) posPowN (by norm_cast)
      have : (u₀ - l₀) / 2 ^ n < (u₀ - l₀) / 2 ^ N := by exact div_lt_div_of_pos_left gap_pos posPow (by norm_cast)
      have : |(u₀ - l₀) / 2 ^ n| < |(u₀ - l₀) / 2 ^ N| := by
        rw [h_abs n, h_abs N]
        exact this
      calc
        |(u₀ - l₀) / 2 ^ n| < |(u₀ - l₀) / 2 ^ N| := this
        _ < ε := by exact lt_of_eq_of_lt (h_abs N) base

  -- pro libovolne n existuje pouze jeden prvek z intervalu (lₙ, uₙ), tady dokazujeme sporem, ze pokud jsou dva, jsou si rovny
  have nested_unique_of_two (s t : ℝ) (hs : ∀ n, lSeq A l₀ u₀ n ≤ s ∧ s ≤ uSeq A l₀ u₀ n) (ht : ∀ n, lSeq A l₀ u₀ n ≤ t ∧ t ≤ uSeq A l₀ u₀ n) : s = t := by
    by_contra hne
    have hpos : 0 < |s - t| := by exact abs_sub_pos.mpr hne
    set ε := |s - t| / 2 with h_ε
    have ε_pos : 0 < ε := by exact half_pos hpos
    obtain ⟨N, hN⟩ := gap_to_0 ε ε_pos
    have hsmall : |(u₀ - l₀) / (2 : ℝ) ^ (N+1)| < ε :=
      hN (N+1) (Nat.lt_succ_self N)
    have hbound : |s - t| ≤ |(u₀ - l₀) / (2 : ℝ) ^ (N+1)| := by
      have st_bound := abs_le_gap s t hs ht (N+1)
      rw [← gap_shrink (N+1)]
      have : uSeq A l₀ u₀ (N + 1) - lSeq A l₀ u₀ (N + 1) ≤ |uSeq A l₀ u₀ (N + 1) - lSeq A l₀ u₀ (N + 1)| := by exact le_abs_self (uSeq A l₀ u₀ (N + 1) - lSeq A l₀ u₀ (N + 1))
      exact Std.le_trans st_bound this
    have contr_1 : |s - t| < ε := lt_of_le_of_lt hbound hsmall
    rw [h_ε] at contr_1
    have contr_2 : ¬ |s - t| < |s - t| / 2 := by
      have hhalf_lt : |s - t| / 2 < |s - t| := half_lt_self hpos
      exact not_lt_of_gt hhalf_lt
    exact contr_2 contr_1

  -- prunik do sebe vlozenych intervalu je prave jeden prvek
  have nestedUnique : ∃! s : ℝ, ∀ n, lSeq A l₀ u₀ n ≤ s ∧ s ≤ uSeq A l₀ u₀ n := by
    obtain ⟨s, hs⟩ := exists_point_in_nested_intervals (l := fun n => lSeq A l₀ u₀ n) (u := fun n => uSeq A l₀ u₀ n) lInc uDec lₙ_leq_uₙ shrink
    have unique : ∀ t, (∀ n, lSeq A l₀ u₀ n ≤ t ∧ t ≤ uSeq A l₀ u₀ n) → t = s := by
      intro t ht
      exact nested_unique_of_two t s ht hs
    exact ⟨s, hs, unique⟩

  obtain ⟨s, hs⟩ := nestedUnique
  -- s je horní závora množiny A
  have upper_s : ∀ a ∈ A, a ≤ s := by
    intro a ha
    -- spor: a > s
    by_contra hnot
    have hgt : s < a := by exact lt_of_not_ge hnot
    -- jen konstatujeme, že z a ≤ s by byl opak; stačí, že máme s < a ⇒ a ≠ s
    have hne : a ≠ s := ne_of_gt hgt
    -- ε = (a - s)/2 > 0
    have hpos : 0 < a - s := sub_pos.mpr hgt
    set ε := (a - s) / 2 with hε
    have ε_pos : 0 < ε := by simpa [hε] using half_pos hpos

    -- z "gap_to_0" vyber N s u_N - l_N < ε (přes tvoje gap_shrink)
    obtain ⟨N, hN⟩ := gap_to_0 ε ε_pos
    -- vezmeme rovnou N+1, ať máme > N
    have gap_small : uSeq A l₀ u₀ (N+1) - lSeq A l₀ u₀ (N+1) < ε := by
      -- |(u₀ - l₀)/2^(N+1)| < ε  ⇒  u_{N+1} - l_{N+1} < ε
      have := hN (N+1) (Nat.lt_succ_self N)
      -- přepiš délku intervalu na frakci
      rw [gap_shrink (N+1)]
      have h_pos : u₀ - l₀ ≥ 0 := by linarith
      simp at this
      have le_abs : (u₀ - l₀) / 2 ^ (N + 1) ≤ |(u₀ - l₀) / 2 ^ (N + 1)| := by exact le_abs_self ((u₀ - l₀) / 2 ^ (N + 1))
      exact lt_of_le_of_lt le_abs this

    -- vztahy k N+1:
    have a_le_u : a ≤ uSeq A l₀ u₀ (N+1) := upperBound (N+1) a ha
    have l_le_s : lSeq A l₀ u₀ (N+1) ≤ s := (hs.1 (N+1)).1
    have s_le_u : s ≤ uSeq A l₀ u₀ (N+1) := (hs.1 (N+1)).2

    -- odhad rozdílu a - s přes délku intervalu
    have as_le_us : a - s ≤ uSeq A l₀ u₀ (N+1) - s := by linarith
    have us_le_gap : uSeq A l₀ u₀ (N+1) - s ≤ uSeq A l₀ u₀ (N+1) - lSeq A l₀ u₀ (N+1) := by linarith
    have as_le_gap : a - s ≤ uSeq A l₀ u₀ (N+1) - lSeq A l₀ u₀ (N+1) := by exact le_trans as_le_us us_le_gap

    -- teď: a - s ≤ gap < ε = (a - s)/2  ⇒ spor
    have h_as_lt_eps : a - s < ε := lt_of_le_of_lt as_le_gap gap_small
    have h_not_lt_half : ¬ a - s < (a - s) / 2 := by exact not_lt_of_ge (half_le_self (le_of_lt hpos))
    exact h_not_lt_half h_as_lt_eps

  have least : ∀ z, (∀ a ∈ A, a ≤ z) → s ≤ z := by
    intro z zUpperBound
    by_contra hgt
    have : s > z := by exact lt_of_not_ge hgt
    have h_pos : 0 < s - z := by exact sub_pos.mpr this

    set ε := (s - z) / 2 with h_ε
    have ε_pos : ε > 0 := by exact half_pos h_pos
    choose a haA hla hau using nestedNonempty
    have l_le_z : ∀ n, lSeq A l₀ u₀ n ≤ z := by
      exact fun n => Std.le_trans (hla n) (zUpperBound (a n) (haA n))
    obtain ⟨N, hN⟩ := gap_to_0 ε ε_pos
    have gap_small : uSeq A l₀ u₀ (N+1) - lSeq A l₀ u₀ (N+1) < ε := by
      have := hN (N+1) (Nat.lt_succ_self N)
      rw [gap_shrink]
      have : (u₀ - l₀) / 2 ^ (N + 1) ≤ |(u₀ - l₀) / 2 ^ (N + 1)| := by exact le_abs_self ((u₀ - l₀) / 2 ^ (N + 1))
      (expose_names; exact lt_of_le_of_lt this this_2)
    have lN_le_s : lSeq A l₀ u₀ N ≤ s := (hs.1 N).1
    have s_le_uN : s ≤ uSeq A l₀ u₀ N := (hs.1 N).2
    have sl_le_gap : s - lSeq A l₀ u₀ N ≤ uSeq A l₀ u₀ N - lSeq A l₀ u₀ N := by linarith
    set lN := lSeq A l₀ u₀ (N+1) with hl
    set uN := uSeq A l₀ u₀ (N+1) with hu

    have l_le_s : lN ≤ s := by simpa [hl] using (hs.1 (N+1)).1
    have s_le_u : s ≤ uN := by simpa [hu] using (hs.1 (N+1)).2

    have sl_le_ul : s - lN ≤ uN - lN := sub_le_sub_right s_le_u lN


    have : s - lN < ε := by exact lt_of_le_of_lt sl_le_ul gap_small
    have : lN > s - ε := by exact sub_lt_comm.mp this
    have s_sub_eps_eq_z : s - ε = z + ε := by rw [h_ε]; ring
    have : lN > z := by linarith [l_le_z (N+1)]
    exact (not_lt_of_ge (l_le_z (N+1))) this

  have hsSup : IsSup A s := by
    unfold IsSup
    intro x hx
    constructor
    · exact upper_s x hx
    · intro ε hε
      -- We need to find a ∈ A such that s - ε < a
      -- Use gap_to_0 to find an interval small enough
      obtain ⟨N, hN⟩ := gap_to_0 ε hε

      -- Get an element from the nested interval at N+1
      obtain ⟨a, ha_mem, ha_lower, ha_upper⟩ := nestedNonempty (N+1)

      use a, ha_mem

      -- Show s - ε < a
      have gap_small : uSeq A l₀ u₀ (N+1) - lSeq A l₀ u₀ (N+1) < ε := by
        have := hN (N+1) (Nat.lt_succ_self N)
        rw [gap_shrink]
        have : (u₀ - l₀) / 2 ^ (N + 1) ≤ |(u₀ - l₀) / 2 ^ (N + 1)| := le_abs_self _
        (expose_names; exact lt_of_le_of_lt this this_1)

      have s_in_interval : lSeq A l₀ u₀ (N+1) ≤ s ∧ s ≤ uSeq A l₀ u₀ (N+1) := hs.1 (N+1)

      -- Since a ≥ lSeq (N+1) and s ≤ uSeq (N+1) and gap < ε
      -- we have s - a ≤ uSeq - lSeq < ε
      -- Thus a > s - ε
      have : s - lSeq A l₀ u₀ (N+1) ≤ uSeq A l₀ u₀ (N+1) - lSeq A l₀ u₀ (N+1) := by linarith [s_in_interval.2]
      have : s - lSeq A l₀ u₀ (N+1) < ε := lt_of_le_of_lt this gap_small
      have : lSeq A l₀ u₀ (N+1) > s - ε := by linarith
      linarith [ha_lower]

  refine ⟨s, hsSup, ?_⟩
  intro t htSup
  apply le_antisymm
  · -- Show t ≤ s: since s is an upper bound and t is the least upper bound
    have t_least : ∀ z, (∀ a ∈ A, a ≤ z) → t ≤ z := by
      intro z hz
      by_contra hgt
      push_neg at hgt
      have : z < t := hgt
      have h_pos : 0 < t - z := sub_pos.mpr this
      set ε := (t - z) / 2
      have ε_pos : ε > 0 := half_pos h_pos
      have hA_local : A.Nonempty := ⟨l₀, hl₀⟩
      obtain ⟨a, ha_mem, ha_close⟩ := (htSup l₀ hl₀).2 ε ε_pos
      have : z < a := by
        have : t - ε = t - (t - z) / 2 := rfl
        have : t - (t - z) / 2 = (t + z) / 2 := by ring
        have : t - ε = (t + z) / 2 := by rw [this]
        have : (t + z) / 2 < a := by linarith [ha_close]
        linarith
      exact (not_lt_of_ge (hz a ha_mem)) this
    exact t_least s upper_s
  · -- Show s ≤ t: since t is a supremum and s is an upper bound
    -- We use that s is the least upper bound (from 'least')
    -- For any upper bound z, s ≤ z
    -- t is an upper bound (from htSup), so s ≤ t
    have t_upper : ∀ a ∈ A, a ≤ t := fun a ha => (htSup a ha).1
    exact least t t_upper

-- #print axioms exists_unique_supremum

end
