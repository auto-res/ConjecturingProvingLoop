

theorem P2_inter_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hP2A : Topology.P2 A) (hP2B : Topology.P2 B) :
    Topology.P2 (A ∩ B) := by
  -- Use the equivalence `P2 A ↔ IsOpen A` for closed sets.
  have hOpenA : IsOpen A :=
    (Topology.P2_closed_iff_open hA_closed).1 hP2A
  have hOpenB : IsOpen B :=
    (Topology.P2_closed_iff_open hB_closed).1 hP2B
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B) := hOpenA.inter hOpenB
  -- Apply `P2` for open sets.
  exact Topology.P2_of_open hOpenInter