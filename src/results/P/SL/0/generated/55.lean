

theorem P2_inter_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P2 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  exact (Topology.isOpen_has_all_Ps (X := X) (A := (A ∩ B : Set X)) hOpen).2.1