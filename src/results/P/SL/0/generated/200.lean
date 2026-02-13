

theorem interior_union_eq_self_of_open {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∪ B : Set X) = (A ∪ B : Set X) := by
  have hOpen : IsOpen (A ∪ B : Set X) := hA.union hB
  simpa [hOpen.interior_eq]