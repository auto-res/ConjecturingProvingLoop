

theorem Topology.P3_inter_three_of_open
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) :
    Topology.P3 (A := A ∩ B ∩ C) := by
  have h_open : IsOpen (A ∩ B ∩ C) := by
    have hAB : IsOpen (A ∩ B) := IsOpen.inter hA hB
    exact IsOpen.inter hAB hC
  exact Topology.P3_of_isOpen (A := A ∩ B ∩ C) h_open