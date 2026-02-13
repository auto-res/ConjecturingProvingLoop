

theorem Topology.P2_inter_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P2 B) :
    Topology.P2 (A ∩ B) := by
  simpa [Set.inter_comm] using
    (Topology.P2_inter_isOpen_right (X := X) (A := B) (B := A) hB hA_open)