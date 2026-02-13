

theorem P3_inter_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hP3A : Topology.P3 A) (hP3B : Topology.P3 B) :
    Topology.P3 (A ∩ B) := by
  -- Translate `P3` for the closed sets `A` and `B` into their openness.
  have hOpenA : IsOpen A :=
    (Topology.P3_closed_iff_open hA_closed).1 hP3A
  have hOpenB : IsOpen B :=
    (Topology.P3_closed_iff_open hB_closed).1 hP3B
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B) := hOpenA.inter hOpenB
  -- Apply `P3` for open sets.
  exact Topology.P3_of_open hOpenInter