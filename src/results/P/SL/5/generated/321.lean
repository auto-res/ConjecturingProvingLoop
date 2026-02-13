

theorem interior_closure_interior_left_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (interior (A : Set X) ∩ B)) ⊆
      interior (closure (interior A)) ∩ interior (closure B) := by
  simpa using
    interior_closure_inter_subset (X := X) (A := interior A) (B := B)