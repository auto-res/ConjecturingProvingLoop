

theorem P1_imp_eq_empty_of_empty_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hIntEmpty : interior A = (∅ : Set X)) :
    A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    have : x ∈ closure (interior A) := hP1 hx
    simpa [hIntEmpty, closure_empty] using this
  · exact Set.empty_subset _