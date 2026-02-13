

theorem Topology.isClosed_P3_implies_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P3 A → interior A = A := by
  intro hClosed hP3
  -- We already have `interior (closure A) = A` under the same hypotheses.
  have h :=
    Topology.isClosed_P3_implies_interior_closure_eq_self
      (A := A) hClosed hP3
  -- Since `A` is closed, `closure A = A`; rewriting yields the desired equality.
  simpa [hClosed.closure_eq] using h