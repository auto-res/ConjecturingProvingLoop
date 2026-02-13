

theorem Topology.isClosed_P2_implies_closure_interior_eq_self {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P2 A → closure (interior A) = A := by
  intro hClosed hP2
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  exact
    Topology.isClosed_P1_implies_closure_interior_eq_self (A := A) hClosed hP1