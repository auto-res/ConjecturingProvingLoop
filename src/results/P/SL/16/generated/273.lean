

theorem Topology.P3_closure_implies_P1_and_P2_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure A) →
      (Topology.P1 (X := X) (closure A) ∧
        Topology.P2 (X := X) (closure A)) := by
  intro hP3
  have hP1 : Topology.P1 (X := X) (closure A) :=
    Topology.P3_closure_implies_P1_closure (X := X) (A := A) hP3
  have hP2 : Topology.P2 (X := X) (closure A) :=
    Topology.P3_closure_implies_P2_closure (X := X) (A := A) hP3
  exact And.intro hP1 hP2