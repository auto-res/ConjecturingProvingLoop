

theorem Topology.P2_of_P1_and_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Dense A → Topology.P2 A := by
  intro hP1 hDense
  have hP3 : Topology.P3 A := Topology.dense_implies_P3 (A := A) hDense
  exact (Topology.P2_iff_P1_and_P3 (A := A)).mpr ⟨hP1, hP3⟩