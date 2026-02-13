

theorem P1_closed_iff_closure_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P1 A ↔ closure (interior A) = A := by
  have h_cl : closure A = A := hA.closure_eq
  have h_equiv := Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)
  simpa [h_cl, eq_comm] using h_equiv