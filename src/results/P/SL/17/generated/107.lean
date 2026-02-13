

theorem Topology.eq_empty_of_P2_and_interior_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) (hInt : interior A = (∅ : Set X)) :
    A = ∅ := by
  apply Set.Subset.antisymm
  ·
    intro x hxA
    have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
    have hEmpty : x ∈ (∅ : Set X) := by
      simpa [hInt, closure_empty, interior_empty] using hxInt
    cases hEmpty
  ·
    exact Set.empty_subset _