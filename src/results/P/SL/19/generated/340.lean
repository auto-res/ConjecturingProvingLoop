

theorem Topology.frontier_inter_compl_eq_empty_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    frontier (A : Set X) ∩ Aᶜ = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxFront, hxCompl⟩
    have hxA : x ∈ A :=
      (Topology.frontier_subset_of_isClosed (A := A) hA) hxFront
    exact ((hxCompl : x ∉ A) hxA).elim
  · exact Set.empty_subset _