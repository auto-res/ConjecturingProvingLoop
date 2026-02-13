

theorem Topology.eq_empty_of_P3_and_interior_closure_empty {X : Type*}
    [TopologicalSpace X] {A : Set X} (hP3 : Topology.P3 A)
    (hInt : interior (closure A) = (∅ : Set X)) : A = ∅ := by
  apply Set.Subset.antisymm
  ·
    intro x hxA
    have : x ∈ interior (closure A) := hP3 hxA
    simpa [hInt] using this
  ·
    exact Set.empty_subset _