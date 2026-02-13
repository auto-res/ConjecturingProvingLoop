

theorem Topology.eq_empty_of_P1_and_interior_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) (hInt : interior A = (∅ : Set X)) :
    A = ∅ := by
  apply Set.Subset.antisymm
  ·
    intro x hxA
    have hx : x ∈ closure (interior A) := hP1 hxA
    simpa [hInt, closure_empty] using hx
  ·
    exact Set.empty_subset _