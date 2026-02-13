

theorem Topology.P3_inter_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hA_P3 : Topology.P3 A) (hB_P3 : Topology.P3 B) :
    Topology.P3 (A ∩ B) := by
  -- From `P3` and closedness, both `A` and `B` are open.
  have hA_open : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed).1 hA_P3
  have hB_open : IsOpen B :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := B) hB_closed).1 hB_P3
  -- The intersection of two open sets is open.
  have hAB_open : IsOpen (A ∩ B) := IsOpen.inter hA_open hB_open
  -- An open set automatically satisfies `P3`.
  exact Topology.isOpen_implies_P3 (X := X) (A := A ∩ B) hAB_open