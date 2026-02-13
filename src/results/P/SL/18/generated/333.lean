

theorem closure_union_closure_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∪ closure (B : Set X)) = closure (A ∪ B) := by
  calc
    closure (A ∪ closure (B : Set X))
        = closure A ∪ closure (closure (B : Set X)) := by
          simpa [closure_union]
    _ = closure A ∪ closure (B : Set X) := by
          simpa [closure_closure]
    _ = closure (A ∪ B) := by
          simpa [closure_union]