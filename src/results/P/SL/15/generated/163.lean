

theorem P2_imp_eq_empty_of_empty_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A)
    (hIntEmpty : interior (closure (interior A)) = (∅ : Set X)) :
    A = (∅ : Set X) := by
  dsimp [Topology.P2] at hP2
  apply Set.Subset.antisymm
  · intro x hx
    have : x ∈ interior (closure (interior A)) := hP2 hx
    simpa [hIntEmpty] using this
  · exact Set.empty_subset _