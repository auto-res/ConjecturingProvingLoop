

theorem Topology.P1_and_P3_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) A → Topology.P3 (X := X) A → Topology.P2 (X := X) A := by
  intro hP1 hP3
  have h_equiv := Topology.P2_iff_P1_and_P3 (X := X) (A := A)
  exact (h_equiv.mpr ⟨hP1, hP3⟩)