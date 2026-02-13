

theorem P123_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hA : Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A)
    (hB : Topology.P1 B ∧ Topology.P2 B ∧ Topology.P3 B) :
    Topology.P1 (A ×ˢ B) ∧ Topology.P2 (A ×ˢ B) ∧ Topology.P3 (A ×ˢ B) := by
  rcases hA with ⟨hP1A, hP2A, hP3A⟩
  rcases hB with ⟨hP1B, hP2B, hP3B⟩
  have hP1Prod : Topology.P1 (A ×ˢ B) := Topology.P1_prod hP1A hP1B
  have hP2Prod : Topology.P2 (A ×ˢ B) := Topology.P2_prod hP2A hP2B
  have hP3Prod : Topology.P3 (A ×ˢ B) := Topology.P3_prod hP3A hP3B
  exact ⟨hP1Prod, hP2Prod, hP3Prod⟩