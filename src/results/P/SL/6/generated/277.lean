

theorem closure_union_of_closures {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (closure (A : Set X) ∪ closure B) = closure A ∪ closure B := by
  calc
    closure (closure (A : Set X) ∪ closure B)
        = closure (closure (A : Set X)) ∪ closure (closure B) := by
          simpa using closure_union (closure (A : Set X)) (closure B)
    _ = closure (A : Set X) ∪ closure B := by
          simpa [closure_closure]