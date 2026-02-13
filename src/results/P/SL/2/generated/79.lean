

theorem Topology.P2_iff_P1_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) :
    Topology.P2 A ↔ Topology.P1 A := by
  have hEquiv := (Topology.P2_iff_P1_and_P3 (A := A))
  constructor
  · intro hP2
    exact ((hEquiv).1 hP2).left
  · intro hP1
    exact (hEquiv).2 ⟨hP1, hP3⟩