

theorem Topology.interior_union_closure_eq_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A ∪ closure A) = interior (closure A) := by
  have hUnion : (A ∪ closure A : Set X) = closure A := by
    have hSub : (A : Set X) ⊆ closure A := subset_closure
    simpa [Set.union_eq_right.2 hSub]
  simpa [hUnion]