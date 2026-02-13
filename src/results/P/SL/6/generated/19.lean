

theorem P3_iff_open_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) : Topology.P3 A ↔ IsOpen A := by
  simpa [hA.closure_eq] using
    (Topology.P3_closure_iff_open_closure (A := A))