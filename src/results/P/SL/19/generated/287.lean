

theorem Topology.interiors_disjoint {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hIntA, hIntAc⟩
    have hA : x ∈ A := interior_subset hIntA
    have hAc : x ∈ Aᶜ := interior_subset hIntAc
    exact (hAc hA).elim
  · exact Set.empty_subset _