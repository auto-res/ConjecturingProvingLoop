

theorem interior_inter_compl_eq_empty {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hA, hAc⟩
    have hA_mem : (x : X) ∈ A := interior_subset hA
    have hAc_mem : (x : X) ∈ (Aᶜ) := interior_subset hAc
    exact (hAc_mem hA_mem).elim
  · exact Set.empty_subset _