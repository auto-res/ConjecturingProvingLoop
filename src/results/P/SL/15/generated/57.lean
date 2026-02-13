

theorem P2_closed_inter {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B) :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∩ B) := by
  intro hP2A hP2B
  -- Using the closedness of `A` and `B`, translate the `P2` property into openness.
  have hOpenA : IsOpen A :=
    (Topology.P2_closed_iff_isOpen (X := X) (A := A) hA_closed).1 hP2A
  have hOpenB : IsOpen B :=
    (Topology.P2_closed_iff_isOpen (X := X) (A := B) hB_closed).1 hP2B
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B) := hOpenA.inter hOpenB
  -- The intersection of two closed sets is closed.
  have hClosedInter : IsClosed (A ∩ B) := hA_closed.inter hB_closed
  -- Convert the openness of the intersection back to the `P2` property.
  exact
    (Topology.P2_closed_iff_isOpen (X := X) (A := A ∩ B) hClosedInter).2 hOpenInter