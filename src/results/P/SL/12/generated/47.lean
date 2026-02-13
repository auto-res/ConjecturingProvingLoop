

theorem Topology.P1_iff_closure_interior_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_closed : IsClosed (A : Set X)) :
    Topology.P1 (X := X) A ↔ closure (interior A) = (A : Set X) := by
  -- Start from the general characterization of `P1`.
  have h_equiv := Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)
  -- Since `A` is closed, `closure A = A`; rewrite and use symmetry of equality.
  simpa [h_closed.closure_eq, eq_comm] using h_equiv