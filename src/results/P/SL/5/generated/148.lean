

theorem interior_inter_eq {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B : Set X) = interior A ∩ interior B := by
  apply le_antisymm
  ·
    exact interior_inter_subset (X := X) (A := A) (B := B)
  ·
    exact interior_interiors_subset_interior_inter (X := X) (A := A) (B := B)