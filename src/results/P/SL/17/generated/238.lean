

theorem Topology.frontier_inter_interior_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} : frontier A ∩ interior A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hFront, hInt⟩
    -- From `x ∈ frontier A` we know `x ∉ interior A`,
    -- contradicting `x ∈ interior A`.
    exact (hFront.2 hInt).elim
  · exact Set.empty_subset _