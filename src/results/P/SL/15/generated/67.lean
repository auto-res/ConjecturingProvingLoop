

theorem P2_imp_eq_empty_of_empty_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hIntEmpty : interior A = (∅ : Set X)) :
    A = (∅ : Set X) := by
  have hInnerEmpty : interior (closure (interior A)) = (∅ : Set X) := by
    simpa [hIntEmpty, closure_empty, interior_empty]
  apply Set.Subset.antisymm
  · intro x hx
    have : x ∈ interior (closure (interior A)) := hP2 hx
    simpa [hInnerEmpty] using this
  · exact Set.empty_subset _