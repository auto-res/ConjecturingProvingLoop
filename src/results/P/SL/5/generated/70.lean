

theorem closure_interior_eq_self_of_closed_and_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP1 : Topology.P1 (X := X) A) :
    closure (interior A) = A := by
  apply le_antisymm
  ·
    have hsubset : closure (interior A) ⊆ closure A :=
      Topology.closure_interior_subset_closure (X := X) A
    simpa [hClosed.closure_eq] using hsubset
  ·
    exact hP1