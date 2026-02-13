

theorem Topology.isClosed_P1_implies_closure_interior_eq_self {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P1 A → closure (interior A) = A := by
  intro hClosed hP1
  have hEq : closure (interior A) = closure A :=
    Topology.P1_implies_closure_interior_eq_closure (A := A) hP1
  simpa [hClosed.closure_eq] using hEq