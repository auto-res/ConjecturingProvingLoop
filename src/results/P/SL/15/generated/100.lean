

theorem P3_closure_and_P1_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P1 A → Topology.P2 A := by
  intro hP3Closure hP1
  have hP3A : Topology.P3 A :=
    Topology.P3_closure_implies_P3 (X := X) (A := A) hP3Closure
  exact
    Topology.P3_and_P1_implies_P2 (X := X) (A := A) hP3A hP1