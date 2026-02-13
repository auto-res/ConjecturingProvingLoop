

theorem Topology.P2_closure_implies_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure A) → Topology.P3 (X := X) (closure A) := by
  intro hP2
  have hEquiv := (Topology.P2_closure_iff_P3_closure (X := X) (A := A))
  exact hEquiv.1 hP2