

theorem closure_union_interiors_eq {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior (B : Set X)) =
      closure (interior (A : Set X) ∪ interior (B : Set X)) := by
  simpa using
    (closure_union (interior (A : Set X)) (interior (B : Set X))).symm