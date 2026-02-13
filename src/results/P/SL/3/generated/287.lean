

theorem closure_union_closure_right {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    closure (A ∪ closure (B : Set X)) = closure (A ∪ B) := by
  calc
    closure (A ∪ closure (B : Set X))
        = closure (A : Set X) ∪ closure (closure (B : Set X)) := by
          simpa using
            closure_union_eq_union_closure (A := A) (B := closure (B : Set X))
    _ = closure (A : Set X) ∪ closure (B : Set X) := by
          simpa [closure_closure]
    _ = closure (A ∪ B) := by
          simpa using
            (closure_union_eq_union_closure (A := A) (B := B)).symm