

theorem Topology.closure_eq_closureInteriorClosure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      closure (A : Set X) = closure (interior (closure (A : Set X))) := by
  intro hP2
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  simpa using
    (Topology.closure_eq_closureInteriorClosure_of_P3 (A := A) hP3)