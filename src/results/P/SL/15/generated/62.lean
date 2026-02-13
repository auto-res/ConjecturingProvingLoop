

theorem P2_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) → Topology.P3 A := by
  intro hP2Closure
  have hP3Closure : Topology.P3 (closure A) :=
    ((Topology.P2_closure_iff_P3_closure (X := X) (A := A)).1 hP2Closure)
  exact Topology.P3_closure_implies_P3 (X := X) (A := A) hP3Closure