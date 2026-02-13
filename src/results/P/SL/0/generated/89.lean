

theorem P1_inter_three_of_open {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) (hC : IsOpen (C : Set X)) :
    Topology.P1 (A ∩ B ∩ C) := by
  have hOpen : IsOpen ((A ∩ B ∩ C) : Set X) := (hA.inter hB).inter hC
  exact (Topology.isOpen_has_all_Ps (X := X) (A := (A ∩ B ∩ C : Set X)) hOpen).1