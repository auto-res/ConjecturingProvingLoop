

theorem eq_empty_of_P1_and_interior_empty {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hIntEmpty : interior A = (∅ : Set X)) :
    A = ∅ := by
  apply Set.Subset.antisymm
  · intro x hxA
    have hxClInt : x ∈ closure (interior A) := hP1 hxA
    have hxClEmpty : x ∈ closure (∅ : Set X) := by
      simpa [hIntEmpty] using hxClInt
    simpa [closure_empty] using hxClEmpty
  · exact Set.empty_subset _