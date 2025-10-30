import LEANprj.Sequences.defs
import LEANprj.Sequences.Theorems.supInfExistence
open Classical
-- v tomto souboru budoou dalsi definice, zavisle na nejakych vetach

noncomputable def Sup (A : Set ℝ) (hA : A.Nonempty) (hUpperBdd : ∃ u : ℝ, ∀ a ∈ A, a ≤ u) : ℝ :=
  choose (exists_unique_supremum A hA hUpperBdd)
noncomputable def Inf (A : Set ℝ) (hA : A.Nonempty) (hLowerBdd : ∃ l : ℝ, ∀ a ∈ A, l ≤ a) : ℝ :=
  choose (exists_unique_infimum A hA hLowerBdd)
