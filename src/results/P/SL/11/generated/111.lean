

theorem P3_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) → Topology.P3 A := by
  intro hP2Cl
  have hP3Cl : Topology.P3 (closure A) :=
    Topology.P2_implies_P3 (A := closure A) hP2Cl
  exact Topology.P3_of_closure (A := A) hP3Cl