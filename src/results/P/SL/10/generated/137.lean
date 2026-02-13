

theorem Topology.interior_inter_interior_compl_eq_empty' {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior A ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxA, hxAc⟩
    have hA : x ∈ A := interior_subset hxA
    have hAc : x ∈ Aᶜ := interior_subset hxAc
    exact (hAc hA).elim
  · exact Set.empty_subset _