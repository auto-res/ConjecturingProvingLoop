

theorem Topology.interior_closure_union_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A ∪ B)) = interior (closure A ∪ closure B) := by
  have h : closure (A ∪ B) = closure A ∪ closure B := by
    simpa using closure_union A B
  simpa [h]