

theorem Topology.P2_inter_three_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) :
    Topology.P2 (A ∩ B ∩ C) := by
  -- Use the existing lemma that an intersection of three open sets satisfies
  -- all three `P` properties, then extract the `P2` component.
  have h :=
    Topology.isOpen_inter_three_satisfies_P1_P2_P3
      (X := X) (A := A) (B := B) (C := C) hA hB hC
  exact h.2.1