

theorem Topology.P3_closure_implies_P1_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure A) → Topology.P1 (X := X) (closure A) := by
  intro hP3
  have hClosed : IsClosed (closure A) := isClosed_closure
  exact Topology.closed_P3_implies_P1 (X := X) (A := closure A) hClosed hP3