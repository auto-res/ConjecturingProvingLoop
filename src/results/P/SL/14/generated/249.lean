

theorem Topology.closureUnion_has_P1_of_P1
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB : Topology.P1 B) :
    Topology.P1 (closure (A ∪ B : Set X)) := by
  have h_union : Topology.P1 (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  simpa using
    Topology.closure_has_P1_of_P1 (X := X) (A := A ∪ B) h_union