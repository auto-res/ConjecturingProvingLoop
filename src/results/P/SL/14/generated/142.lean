

theorem Topology.P3_union_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P3 B) :
    Topology.P3 (A ∪ B) := by
  have h :=
    Topology.P3_union_isOpen_right (X := X) (A := B) (B := A) hB hA_open
  simpa [Set.union_comm] using h