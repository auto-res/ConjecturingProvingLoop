

theorem P3_closure_iff_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) ↔ Topology.P2 (closure A) := by
  have h_closed : IsClosed (closure A) := isClosed_closure
  have h_equiv := Topology.closed_P2_iff_P3 (X := X) (A := closure A) h_closed
  simpa [h_equiv] using h_equiv.symm