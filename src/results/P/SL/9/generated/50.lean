

theorem Topology.P3_inter_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hP3A : Topology.P3 (A := A)) (hP3B : Topology.P3 (A := B)) :
    Topology.P3 (A := A ∩ B) := by
  -- From `P3` and closedness, `A` and `B` are open.
  have hA_open : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA_closed).1 hP3A
  have hB_open : IsOpen B :=
    (Topology.P3_iff_isOpen_of_isClosed (A := B) hB_closed).1 hP3B
  -- The intersection of two open sets is open.
  have h_inter_open : IsOpen (A ∩ B) := IsOpen.inter hA_open hB_open
  -- Any open set satisfies `P3`.
  exact Topology.P3_of_isOpen (A := A ∩ B) h_inter_open