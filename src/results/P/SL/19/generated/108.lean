

theorem Topology.closure_eq_closure_interior_of_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    Topology.P3 (A := A) → closure A = closure (interior A) := by
  intro hP3
  have hP2 : Topology.P2 (A := A) :=
    (Topology.P3_implies_P2_of_isClosed (A := A) hA) hP3
  exact Topology.closure_eq_closure_interior_of_P2 (A := A) hP2