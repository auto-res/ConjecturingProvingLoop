

theorem P2_iff_P1_for_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense A) : Topology.P2 A ↔ Topology.P1 A := by
  constructor
  · intro hP2
    exact P2_implies_P1 (A := A) hP2
  · intro hP1
    have hP3 : P3 A := P3_of_dense (A := A) h
    exact (P2_iff_P1_and_P3 (A := A)).mpr ⟨hP1, hP3⟩