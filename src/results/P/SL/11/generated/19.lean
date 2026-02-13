

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 A) (hB : Topology.P2 B) :
    Topology.P2 (A ∪ B) := by
  have hP1A : Topology.P1 A := Topology.P2_implies_P1 hA
  have hP1B : Topology.P1 B := Topology.P2_implies_P1 hB
  have hP3A : Topology.P3 A := Topology.P2_implies_P3 hA
  have hP3B : Topology.P3 B := Topology.P2_implies_P3 hB
  have hP1Union : Topology.P1 (A ∪ B) := Topology.P1_union hP1A hP1B
  have hP3Union : Topology.P3 (A ∪ B) := Topology.P3_union hP3A hP3B
  exact Topology.P2_of_P1_and_P3 (A := A ∪ B) ⟨hP1Union, hP3Union⟩