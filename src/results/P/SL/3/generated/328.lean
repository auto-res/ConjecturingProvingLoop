

theorem closure_union_three {X : Type*} [TopologicalSpace X]
    (A B C : Set X) :
    closure ((A ∪ B ∪ C) : Set X) =
      closure (A : Set X) ∪ closure B ∪ closure C := by
  calc
    closure ((A ∪ B ∪ C) : Set X)
        = closure (((A ∪ B) ∪ C) : Set X) := by
          simpa [Set.union_assoc]
    _ = closure (A ∪ B : Set X) ∪ closure C := by
          simpa using
            (closure_union_eq_union_closure
              (A := (A ∪ B)) (B := C))
    _ = (closure A ∪ closure B) ∪ closure C := by
          simpa
            [closure_union_eq_union_closure (A := A) (B := B)]
    _ = closure (A : Set X) ∪ closure B ∪ closure C := by
          simpa [Set.union_assoc]