

theorem closure_union_interior_eq_union_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ B) = closure (interior A) ∪ closure B := by
  simpa using (closure_union (s := interior A) (t := B))