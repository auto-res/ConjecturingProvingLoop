

theorem P3_closure_iff_P3_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 (closure (A : Set X)) ↔ Topology.P3 A := by
  have hEq : closure (A : Set X) = A := hA.closure_eq
  simpa [hEq] using
    (Iff.rfl :
      Topology.P3 (closure (A : Set X)) ↔ Topology.P3 (closure (A : Set X)))