

theorem P123_union_left_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P1 B ∧ Topology.P2 B ∧ Topology.P3 B) :
    Topology.P1 (A ∪ B) ∧ Topology.P2 (A ∪ B) ∧ Topology.P3 (A ∪ B) := by
  simpa [Set.union_comm] using
    (Topology.P123_union_right_open (A := B) (B := A) hB hA_open)