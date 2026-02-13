

theorem closures_union_three_eq_closure_union_three
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    closure (A : Set X) ∪ closure (B : Set X) ∪ closure (C : Set X) =
      closure (A ∪ B ∪ C : Set X) := by
  calc
    (closure (A : Set X)) ∪ closure (B : Set X) ∪ closure (C : Set X)
        = (closure (A : Set X) ∪ closure (B : Set X)) ∪ closure (C : Set X) := by
          simpa [Set.union_assoc]
    _ = closure (A ∪ B : Set X) ∪ closure (C : Set X) := by
          simpa [closure_union]
    _ = closure ((A ∪ B) ∪ C : Set X) := by
          simpa [closure_union]
    _ = closure (A ∪ B ∪ C : Set X) := by
          simpa [Set.union_assoc]