

theorem Topology.P3_inter_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∩ B) := by
  intro hP3A hP3B
  have hOpenA : IsOpen A :=
    (Topology.P3_closed_iff_isOpen (A := A) hA).1 hP3A
  have hOpenB : IsOpen B :=
    (Topology.P3_closed_iff_isOpen (A := B) hB).1 hP3B
  have hOpenAB : IsOpen (A ∩ B) := hOpenA.inter hOpenB
  have hClosedAB : IsClosed (A ∩ B) := hA.inter hB
  exact
    (Topology.P3_closed_iff_isOpen (A := A ∩ B) hClosedAB).2 hOpenAB