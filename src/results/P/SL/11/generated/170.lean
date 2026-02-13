

theorem eq_empty_of_P2_and_interior_empty {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hIntEmpty : interior A = (∅ : Set X)) :
    A = ∅ := by
  apply Set.Subset.antisymm
  · intro x hxA
    have hxInner : x ∈ interior (closure (interior A)) := hP2 hxA
    simpa [hIntEmpty, closure_empty, interior_empty] using hxInner
  · exact Set.empty_subset _