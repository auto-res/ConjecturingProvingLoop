

theorem closure_interior_eq_of_closed_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP3 : Topology.P3 A) :
    closure (interior A) = A := by
  have hInt : interior A = A :=
    interior_eq_self_of_closed_of_P3 (A := A) hA hP3
  simpa [hInt, hA.closure_eq]