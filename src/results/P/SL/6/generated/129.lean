

theorem closure_interior_union_eq_closure_union_of_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    closure (interior (A ∪ B : Set X)) = closure (A ∪ B) := by
  have hInt : interior (A ∪ B : Set X) = A ∪ B :=
    (hA.union hB).interior_eq
  simpa [hInt]