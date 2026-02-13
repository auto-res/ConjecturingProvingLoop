

theorem Topology.P1_inter_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) : Topology.P1 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  exact Topology.P1_of_isOpen (A := A ∩ B) hOpen