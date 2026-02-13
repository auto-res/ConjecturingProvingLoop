

theorem P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB : Topology.P1 B) :
    Topology.P1 (closure (A ∪ B : Set X)) := by
  have hUnion : Topology.P1 (A ∪ B) :=
    Topology.P1_union (A := A) (B := B) hA hB
  exact Topology.P1_closure_of_P1 (A := A ∪ B) hUnion