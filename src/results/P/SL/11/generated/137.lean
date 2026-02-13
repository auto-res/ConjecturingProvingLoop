

theorem P3_union_left_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P3 B) :
    Topology.P3 (A ∪ B) := by
  simpa [Set.union_comm] using
    (Topology.P3_union_right_open (A := B) (B := A) hB hA_open)