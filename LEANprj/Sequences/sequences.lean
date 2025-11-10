import LEANprj.Sequences.defs
import LEANprj.Sequences.Theorems.SupInfExistence
open Classical
-- v tomto souboru budoou dalsi definice, zavisle na nejakych vetach

noncomputable def Sup (A : Set ℝ) (hA : A.Nonempty) (hUpperBdd : ∃ u : ℝ, ∀ a ∈ A, a ≤ u) : ℝ :=
  choose (exists_unique_supremum A hA hUpperBdd)
noncomputable def Inf (A : Set ℝ) (hA : A.Nonempty) (hLowerBdd : ∃ l : ℝ, ∀ a ∈ A, l ≤ a) : ℝ :=
  choose (exists_unique_infimum A hA hLowerBdd)

noncomputable def SupSeq (a : ℕ → ℝ) (hne : (Set.range a).Nonempty) (ha_upper_bdd : ∃ u : ℝ, ∀ c ∈ (Set.range a), c ≤ u) := Sup (Set.range a) hne ha_upper_bdd
noncomputable def InfSeq (a : ℕ → ℝ) (hne : (Set.range a).Nonempty) (ha_lower_bdd : ∃ u : ℝ, ∀ c ∈ (Set.range a), c ≥ u) := Inf (Set.range a) hne ha_lower_bdd

lemma Sup_isSup (A : Set ℝ) (hA : A.Nonempty) (hB : ∃ u : ℝ, ∀ a ∈ A, a ≤ u) : IsSup A (Sup A hA hB) := by
  have hspec : IsSup A (choose (exists_unique_supremum A hA hB)) := (choose_spec (exists_unique_supremum A hA hB)).1
  simpa

lemma Inf_IsInf (A : Set ℝ) (hA : A.Nonempty) (hB : ∃ u : ℝ, ∀ a ∈ A, a ≥ u) : IsInf A (Inf A hA hB) := by
  have hspec : IsInf A (choose (exists_unique_infimum A hA hB)) := (choose_spec (exists_unique_infimum A hA hB)).1
  simpa
