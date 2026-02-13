

theorem Topology.interior_closure_union_eq_interior_union_closures
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    interior (closure (A ∪ B : Set X)) =
      interior (closure A ∪ closure B) := by
  simp [closure_union]