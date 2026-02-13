

theorem P1_closure_iff_P1_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P1 (closure (A : Set X)) ↔ Topology.P1 A := by
  have hEq : closure (A : Set X) = A := hA.closure_eq
  simpa [hEq] using
    (Iff.rfl : Topology.P1 (closure (A : Set X)) ↔ Topology.P1 (closure (A : Set X)))