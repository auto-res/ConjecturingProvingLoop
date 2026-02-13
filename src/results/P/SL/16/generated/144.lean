

theorem Topology.P2_closure_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure A) → Topology.P1 (X := X) (closure A) := by
  intro hP2
  have hClosed : IsClosed (closure A) := isClosed_closure
  exact Topology.closed_P2_implies_P1 (X := X) (A := closure A) hClosed hP2