

theorem closure_union_closure_closure {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    closure (closure (A : Set X) ∪ closure (B : Set X)) =
      closure (A ∪ B) := by
  calc
    closure (closure (A : Set X) ∪ closure (B : Set X))
        = closure (A ∪ closure (B : Set X)) := by
          simpa using
            closure_union_closure_left (A := A) (B := closure (B : Set X))
    _ = closure (A ∪ B) := by
          simpa using
            closure_union_closure_right (A := A) (B := B)