

theorem Topology.P1_iff_eq_closure_interior_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    Topology.P1 (A := A) ↔ A = closure (interior A) := by
  simpa [hA.closure_eq] using
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A))