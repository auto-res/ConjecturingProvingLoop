

theorem interior_eq_self_of_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP3 : Topology.P3 A) :
    interior A = A := by
  apply subset_antisymm
  · exact interior_subset
  ·
    have h : (A : Set X) ⊆ interior (closure A) := hP3
    simpa [hA.closure_eq] using h