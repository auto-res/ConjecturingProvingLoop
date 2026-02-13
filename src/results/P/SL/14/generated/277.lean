

theorem Topology.P1_inter_three_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) :
    Topology.P1 (A ∩ B ∩ C) := by
  exact
    (Topology.isOpen_inter_three_satisfies_P1_P2_P3
      (X := X) (A := A) (B := B) (C := C) hA hB hC).1