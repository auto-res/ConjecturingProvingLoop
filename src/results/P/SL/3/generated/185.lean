

theorem interior_inter_eq_interiors {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior ((A ∩ B) : Set X) =
      interior (A : Set X) ∩ interior (B : Set X) := by
  apply Set.Subset.antisymm
  · exact interior_inter_subset_interiors (A := A) (B := B)
  · intro x hx
    exact (inter_interiors_subset_interior_inter (A := A) (B := B)) hx