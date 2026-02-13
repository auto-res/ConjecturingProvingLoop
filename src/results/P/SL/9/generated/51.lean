

theorem Topology.P2_inter_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P2 (A := A ∩ B) := by
  have h_open : IsOpen (A ∩ B) := IsOpen.inter hA hB
  exact Topology.P2_of_isOpen (A := A ∩ B) h_open