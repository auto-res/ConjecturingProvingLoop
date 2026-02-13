

theorem isOpen_inter_implies_P2 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P2 (X := X) (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  exact Topology.isOpen_implies_P2 (X := X) (A := A ∩ B) hOpen