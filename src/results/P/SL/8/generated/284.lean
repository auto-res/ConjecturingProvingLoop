

theorem P1_union_closure {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB : Topology.P1 B) :
    Topology.P1 (closure (A ∪ B)) := by
  have hUnion : Topology.P1 (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  have hCl : Topology.P1 (closure (A ∪ B)) :=
    Topology.P1_imp_P1_closure (X := X) (A := A ∪ B) hUnion
  simpa using hCl