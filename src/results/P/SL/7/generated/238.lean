

theorem Topology.P2_closure_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔
      interior (closure (A : Set X)) = closure (A : Set X) := by
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using
    (Topology.P2_closed_iff_interior_eq (A := closure (A : Set X)) hClosed)