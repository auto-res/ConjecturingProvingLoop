

theorem Topology.P2_inter_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hP2A : Topology.P2 (A := A)) (hP2B : Topology.P2 (A := B)) :
    Topology.P2 (A := A ∩ B) := by
  -- From `P2`, derive `P3`, and using closedness convert to openness.
  have hA_open : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA_closed).1
      (Topology.P2_implies_P3 hP2A)
  have hB_open : IsOpen B :=
    (Topology.P3_iff_isOpen_of_isClosed (A := B) hB_closed).1
      (Topology.P2_implies_P3 hP2B)
  -- The intersection of two open sets is open.
  have h_inter_open : IsOpen (A ∩ B) := IsOpen.inter hA_open hB_open
  -- Any open set satisfies `P2`.
  exact Topology.P2_of_isOpen (A := A ∩ B) h_inter_open