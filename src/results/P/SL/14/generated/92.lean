

theorem Topology.P2_inter_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hA_P2 : Topology.P2 A) (hB_P2 : Topology.P2 B) :
    Topology.P2 (A ∩ B) := by
  -- From `P2` and closedness we deduce that both `A` and `B` are open.
  have hA_open : IsOpen A :=
    Topology.isOpen_of_isClosed_and_P2 (X := X) (A := A) hA_closed hA_P2
  have hB_open : IsOpen B :=
    Topology.isOpen_of_isClosed_and_P2 (X := X) (A := B) hB_closed hB_P2
  -- The intersection of two open sets is open.
  have hAB_open : IsOpen (A ∩ B) := IsOpen.inter hA_open hB_open
  -- Any open set satisfies `P2`.
  exact Topology.isOpen_implies_P2 (X := X) (A := A ∩ B) hAB_open