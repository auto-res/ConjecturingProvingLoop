

theorem Topology.interior_inter_compl_eq_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hA, hAc⟩
    have hA_mem : x ∈ A := interior_subset hA
    have hAc_mem : x ∈ Aᶜ := interior_subset hAc
    have : x ∈ A ∩ Aᶜ := ⟨hA_mem, hAc_mem⟩
    simpa [Set.inter_compl_self] using this
  · exact Set.empty_subset _