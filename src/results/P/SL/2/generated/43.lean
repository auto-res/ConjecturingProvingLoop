

theorem Topology.P2_iff_P1_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → (Topology.P2 A ↔ Topology.P1 A) := by
  intro hDense
  have hP3 : Topology.P3 A := Topology.dense_implies_P3 (A := A) hDense
  have hEquiv := (Topology.P2_iff_P1_and_P3 (A := A))
  constructor
  · intro hP2
    exact (Topology.P2_implies_P1 (A := A) hP2)
  · intro hP1
    have : Topology.P1 A ∧ Topology.P3 A := And.intro hP1 hP3
    exact (hEquiv).2 this