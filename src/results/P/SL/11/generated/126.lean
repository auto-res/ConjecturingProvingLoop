

theorem P2_union_left_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P2 B) :
    Topology.P2 (A ∪ B) := by
  simpa [Set.union_comm] using
    (Topology.P2_union_right_open (A := B) (B := A) hB hA_open)