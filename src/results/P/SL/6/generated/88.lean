

theorem P2_closure_iff_P2_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 (closure (A : Set X)) ↔ Topology.P2 A := by
  have hEq : closure (A : Set X) = A := hA.closure_eq
  simpa [hEq] using
    (Iff.rfl :
      Topology.P2 (closure (A : Set X)) ↔ Topology.P2 (closure (A : Set X)))