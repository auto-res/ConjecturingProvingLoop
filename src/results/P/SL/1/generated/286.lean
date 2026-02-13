

theorem Topology.interior_eq_of_isClosed_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP3 : Topology.P3 A) :
    interior A = A := by
  have h := Topology.interior_closure_eq_of_isClosed_of_P3 (A := A) hA hP3
  simpa [hA.closure_eq] using h