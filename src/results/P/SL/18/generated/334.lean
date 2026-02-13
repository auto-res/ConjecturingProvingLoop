

theorem closure_union_closure_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (closure (A : Set X) ∪ B) = closure (A ∪ B) := by
  calc
    closure (closure (A : Set X) ∪ B)
        = closure (closure (A : Set X)) ∪ closure B := by
          simpa [closure_union]
    _ = closure (A : Set X) ∪ closure B := by
          simpa [closure_closure]
    _ = closure (A ∪ B : Set X) := by
          simpa [closure_union]