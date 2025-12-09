import LEANprj.defs
open Classical
noncomputable section


theorem ConvImpliesBdd {a : ℕ → ℝ} (a_conv : Convergent a) : BoundedSequence a := by
  unfold BoundedSequence
  unfold Convergent ConvergesTo at a_conv
  obtain ⟨q, hq⟩ := a_conv
  -- pouzijeme ε = 1
  obtain ⟨n₀, hn₀⟩ := hq 1 (by linarith)
  -- zavedeme konecnou mnozinu prvnich n prvku
  let S : Finset ℝ := (Finset.range n₀).image (λ n => |a n|)
  -- vime, ze S je bud neprazdna nebo prazdna
  have S_nonempty_or : S.Nonempty ∨ ¬S.Nonempty := by exact Decidable.em S.Nonempty

  -- zavedeme K₁ jako max S pokud je neprazdan, jinak 0
  let K₁ : ℝ := if h : S.Nonempty then S.max' h else 0
  -- zavedeme K jako maximum z (K₁ a (|q| + 1)) + 1, ktere jiste vime, ze omezuje zbytek posloupnosti
  let K : ℝ := max K₁ (|q| + 1) + 1
  use K
  constructor
  · -- nejprve ukazeme ze K > 0
    have : 0 ≤ max K₁ (|q| + 1) := by exact le_max_of_le_right (by have := abs_nonneg q; linarith)
    have : 0 < max K₁ (|q| + 1) + 1 := by exact add_pos_of_nonneg_of_pos this (by norm_num)
    simpa
  · -- a dale, ze K je horni zavora pro celou posloupnost
    intro n
    by_cases hn : n₀ ≤ n
    · -- ukazem, ze vsechny prvky za n₀ jsou omezene
      have htri : |a n| ≤ |a n - q| + |q| := by simpa using (abs_add (a n - q) q)
      have h_lt_1 : |a n - q| < 1 := by exact hn₀ n hn
      have : |a n| < 1 + |q| := by calc
        |a n| ≤ |a n - q| + |q| := by exact htri
        _ < 1 + |q| := by exact (add_lt_add_iff_right |q|).mpr (h_lt_1)
      have : |q| + 1 < max K₁ (|q| + 1) + 1 := by
        have : |q| + 1 ≤ max K₁ (|q| + 1) := by exact le_max_right _ _
        exact lt_of_le_of_lt this (by linarith)
      have := calc
        |a n| < 1 + |q| := by (expose_names; exact this_1)
        _ = |q| + 1 := by ring
        _ < max K₁ (|q| + 1) + 1 := by linarith
      dsimp [K]
      exact le_of_lt this
    · -- a ze i zbytek (tj. prvky pred n₀) je omezeny stejnou konstantou
      have hnlt : n < n₀ := by linarith
      have hmem : |a n| ∈ S := by
        have : n ∈ Finset.range n₀ := Finset.mem_range.mpr hnlt
        simpa [S] using Finset.mem_image.mpr ⟨n, this, rfl⟩

      have hS : S.Nonempty := ⟨|a n|, hmem⟩
      have h_le_K₁ : |a n| ≤ K₁ := by
        simp only [K₁, hS, dite_true]
        exact Finset.le_max' S |a n| hmem
      have K₁_le_K : K₁ < K := by
        have : K₁ ≤ max K₁ (|q| + 1) := by exact le_max_left K₁ (|q| + 1)
        have : K₁ < max K₁ (|q| + 1) + 1 := by exact lt_of_le_of_lt this (by linarith)
        exact this
      calc |a n|
      _ ≤ K₁ := by exact h_le_K₁
      _ ≤ K := by exact le_of_lt K₁_le_K
