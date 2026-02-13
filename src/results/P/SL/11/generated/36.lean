

theorem closure_eq_closure_interior_of_P1_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : Topology.P1 A) (hB : Topology.P1 B) :
    closure (A ∪ B) = closure (interior (A ∪ B)) := by
  have hUnion : Topology.P1 (A ∪ B) := Topology.P1_union hA hB
  exact Topology.closure_eq_closure_interior_of_P1 (A := A ∪ B) hUnion