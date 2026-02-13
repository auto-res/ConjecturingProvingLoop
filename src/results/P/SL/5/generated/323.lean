

theorem interior_closure_union_eq {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∪ B : Set X)) = interior (closure A ∪ closure B) := by
  simpa using
    congrArg interior
      (closure_union (A := (A : Set X)) (B := B))