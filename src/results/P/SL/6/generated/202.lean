

theorem P2_union_of_P2_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P2 (A ∪ B) := by
  have hB₂ : Topology.P2 (B : Set X) :=
    Topology.open_satisfies_P2 (A := B) hB
  exact Topology.P2_union_of_P2 (A := A) (B := B) hA hB₂