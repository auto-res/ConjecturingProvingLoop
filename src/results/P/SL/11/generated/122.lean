

theorem P3_inter_left_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P3 B) :
    Topology.P3 (A ∩ B) := by
  simpa [Set.inter_comm] using
    (Topology.P3_inter_right_open (A := B) (B := A) hB hA_open)