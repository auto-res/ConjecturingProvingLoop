

theorem Topology.P2_inter_three_closed
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hC : IsClosed C) :
    Topology.P2 A → Topology.P2 B → Topology.P2 C →
    Topology.P2 (A ∩ B ∩ C) := by
  intro hP2A hP2B hP2C
  -- Turn the `P2` hypotheses on the three closed sets into openness.
  have hOpenA : IsOpen A :=
    (Topology.P2_closed_iff_isOpen (A := A) hA).1 hP2A
  have hOpenB : IsOpen B :=
    (Topology.P2_closed_iff_isOpen (A := B) hB).1 hP2B
  have hOpenC : IsOpen C :=
    (Topology.P2_closed_iff_isOpen (A := C) hC).1 hP2C
  -- The triple intersection of the open sets is itself open.
  have hOpenABC : IsOpen (A ∩ B ∩ C) := by
    have hOpenAB : IsOpen (A ∩ B) := hOpenA.inter hOpenB
    exact hOpenAB.inter hOpenC
  -- An open set satisfies `P2`.
  exact IsOpen_P2 (A := A ∩ B ∩ C) hOpenABC