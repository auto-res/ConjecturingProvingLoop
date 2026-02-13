

theorem Topology.P2_inter_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∩ B) := by
  intro hP2A hP2B
  have hOpenA : IsOpen A :=
    (Topology.P2_closed_iff_isOpen (A := A) hA).1 hP2A
  have hOpenB : IsOpen B :=
    (Topology.P2_closed_iff_isOpen (A := B) hB).1 hP2B
  have hOpenAB : IsOpen (A ∩ B) := hOpenA.inter hOpenB
  exact IsOpen_P2 (A := A ∩ B) hOpenAB