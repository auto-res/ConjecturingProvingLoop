

theorem open_inter_satisfies_P2 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P2 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  exact Topology.open_satisfies_P2 (A := A ∩ B) hOpen