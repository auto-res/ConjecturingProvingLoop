

theorem Topology.P2_inter_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) : Topology.P2 (A ∩ B) := by
  simpa using
    (Topology.isOpen_inter_satisfies_P1_P2_P3 (X := X) (A := A) (B := B) hA hB).2.1