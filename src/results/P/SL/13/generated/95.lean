

theorem Topology.P2_inter_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P2 (X := X) (A ∩ B) := by
  have h_open : IsOpen ((A ∩ B) : Set X) := hA.inter hB
  exact isOpen_implies_P2 (X := X) (A := A ∩ B) h_open