

theorem interior_closure_union_three_eq {X : Type*} [TopologicalSpace X]
    {A B C : Set X} :
    interior (closure ((A ∪ B ∪ C) : Set X)) =
      interior (closure (A : Set X) ∪ closure (B : Set X) ∪ closure (C : Set X)) := by
  calc
    interior (closure ((A ∪ B ∪ C) : Set X)) =
        interior (closure (((A ∪ B) ∪ C) : Set X)) := by
          simpa [Set.union_assoc]
    _ = interior (closure ((A ∪ B) : Set X) ∪ closure (C : Set X)) := by
          simpa using
            (interior_closure_union_eq (X := X) (A := A ∪ B) (B := C))
    _ = interior ((closure (A : Set X) ∪ closure (B : Set X)) ∪
        closure (C : Set X)) := by
          have h_cl :
              closure ((A ∪ B) : Set X) =
                closure (A : Set X) ∪ closure (B : Set X) := by
            simpa [closure_union]
          simpa [h_cl]
    _ = interior (closure (A : Set X) ∪ closure (B : Set X) ∪
        closure (C : Set X)) := by
          simpa [Set.union_assoc]