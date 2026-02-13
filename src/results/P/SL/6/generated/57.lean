

theorem P1_closure_union_of_P1
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (A : Set X)) (hB : Topology.P1 (B : Set X)) :
    Topology.P1 (closure (A ∪ B : Set X)) := by
  -- First, `P1` holds for the union `A ∪ B`.
  have hUnion : Topology.P1 (A ∪ B : Set X) :=
    Topology.P1_union_of_P1 (A := A) (B := B) hA hB
  -- Then, apply the closure-stability of `P1`.
  exact Topology.P1_closure_of_P1 (A := A ∪ B) hUnion