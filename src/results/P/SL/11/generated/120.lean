

theorem P1_inter_left_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P1 B) :
    Topology.P1 (A ∩ B) := by
  simpa [Set.inter_comm] using
    (Topology.P1_inter_right_open (A := B) (B := A) hB hA_open)