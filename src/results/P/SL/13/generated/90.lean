

theorem Topology.P1_inter_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P1 (X := X) (A ∩ B) := by
  have h_open : IsOpen ((A ∩ B) : Set X) := hA.inter hB
  exact isOpen_subset_closureInterior (X := X) (A := A ∩ B) h_open