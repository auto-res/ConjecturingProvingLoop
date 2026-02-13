

theorem Topology.isOpen_inter_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P1 (A ∩ B) ∧ Topology.P2 (A ∩ B) ∧ Topology.P3 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := IsOpen.inter hA hB
  exact
    Topology.isOpen_satisfies_P1_P2_P3
      (X := X) (A := A ∩ B) hOpen