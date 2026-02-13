

theorem Topology.P3_inter_three_closed
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hC : IsClosed C) :
    Topology.P3 A → Topology.P3 B → Topology.P3 C →
    Topology.P3 (A ∩ B ∩ C) := by
  intro hP3A hP3B hP3C
  -- Convert `P3` on closed sets to openness.
  have hOpenA : IsOpen A :=
    (Topology.P3_closed_iff_isOpen (A := A) hA).1 hP3A
  have hOpenB : IsOpen B :=
    (Topology.P3_closed_iff_isOpen (A := B) hB).1 hP3B
  have hOpenC : IsOpen C :=
    (Topology.P3_closed_iff_isOpen (A := C) hC).1 hP3C
  -- The intersection of the three open sets is open.
  have hOpenABC : IsOpen (A ∩ B ∩ C) := by
    have hAB : IsOpen (A ∩ B) := hOpenA.inter hOpenB
    exact hAB.inter hOpenC
  -- The same intersection is closed as an intersection of closed sets.
  have hClosedABC : IsClosed (A ∩ B ∩ C) := by
    have hAB : IsClosed (A ∩ B) := hA.inter hB
    exact hAB.inter hC
  -- Use the closed-set characterisation `P3 ↔ IsOpen` to obtain `P3`.
  exact
    (Topology.P3_closed_iff_isOpen (A := A ∩ B ∩ C) hClosedABC).2 hOpenABC