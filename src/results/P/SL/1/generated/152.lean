

theorem interior_union
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    interior (A ∪ B : Set X) = interior (A ∪ B) :=
  rfl