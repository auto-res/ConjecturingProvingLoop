

theorem Topology.P3_iff_isOpen_of_closure_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hcl : closure (A : Set X) = A) :
    Topology.P3 A ↔ IsOpen A := by
  -- First, note that `A` is closed because it is equal to its closure.
  have hClosed : IsClosed (A : Set X) := by
    simpa [hcl] using (isClosed_closure : IsClosed (closure (A : Set X)))
  -- Apply the characterisation for closed sets.
  simpa using (Topology.P3_closed_iff_isOpen (A := A) hClosed)