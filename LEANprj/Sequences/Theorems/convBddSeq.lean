import LEANprj.Sequences.sequences
open Classical
noncomputable section


theorem convImpBdd (a : ℕ → ℝ) (a_conv : Convergent a) : BoundedSequence a := by
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
  -- zavedeme K jako maximum z K₁ a (|q| + 1) + 1, ktere jiste vime, ze omezuje zbytek posloupnosti
  let K : ℝ := max K₁ (|q| + 1) + 1
  use K
  constructor
  · have : 0 ≤ max K₁ (|q| + 1) := by exact le_max_of_le_right (by have := abs_nonneg q; linarith)
    have : 0 < max K₁ (|q| + 1) + 1 := by exact add_pos_of_nonneg_of_pos this (by norm_num)
    simpa
  ·
    sorry


  -- -- mez pro prvky posloupnosti > n₀
  -- let K_n₀ := 1 + |q|
  -- -- prvnich n₀ prvku posloupnosti v absolutni hodnote
  -- let head_values := List.map (λ i => |a i|) (List.range n₀)
  -- -- spojime prvni prvky s mezi pro zbytek
  -- let all_values := head_values ++ [K_n₀]
  -- -- vime, ze tento seznam prvku je neprazdny, protoze vzdy obsahuje alespon K_n₀
  -- have h_nonempty : all_values ≠ [] := by exact List.concat_ne_nil K_n₀ head_values
  -- -- vezmeme maximum z tohoto seznamu (fold nam vzdy pouzije max na jeden prvek a vrati ho, tj vezme prvni a porovna ho s nulou a brati vetsi, ktery pak porovna taky s nulou a vrati vetsi, takto najdu maximum konecneho seznamu)
  -- let k := all_values.foldl max 0
  -- let K := k + 1
  -- use K
  -- constructor
  -- · have k_gt_Kn₀ : k ≥ K_n₀ := by


  --     sorry
  --   sorry
  -- ·
  --   sorry
