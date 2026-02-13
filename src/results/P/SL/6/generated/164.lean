

theorem open_union_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P1 (A ∪ B) ∧ Topology.P2 (A ∪ B) ∧ Topology.P3 (A ∪ B) := by
  have hOpen : IsOpen (A ∪ B : Set X) := hA.union hB
  exact Topology.open_satisfies_all_Ps (A := A ∪ B) hOpen