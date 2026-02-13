

theorem closures_union_four_eq_closure_union_four {X : Type*} [TopologicalSpace X]
    {A B C D : Set X} :
    closure (A : Set X) ∪ closure (B : Set X) ∪ closure (C : Set X) ∪ closure (D : Set X) =
      closure (A ∪ B ∪ C ∪ D : Set X) := by
  calc
    (closure (A : Set X)) ∪ closure (B : Set X) ∪ closure (C : Set X) ∪ closure (D : Set X)
        = ((closure (A : Set X) ∪ closure (B : Set X)) ∪ closure (C : Set X)) ∪
            closure (D : Set X) := by
          simpa [Set.union_assoc]
    _ = (closure (A ∪ B : Set X) ∪ closure (C : Set X)) ∪ closure (D : Set X) := by
          simpa [closure_union]
    _ = closure (A ∪ B ∪ C : Set X) ∪ closure (D : Set X) := by
          simpa [Set.union_assoc, closure_union]
    _ = closure ((A ∪ B ∪ C) ∪ D : Set X) := by
          simpa [closure_union]
    _ = closure (A ∪ B ∪ C ∪ D : Set X) := by
          simpa [Set.union_assoc]