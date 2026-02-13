

theorem closure_interInterior_subset_closureInterior_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ interior B) ⊆ closure (interior (A ∩ B)) := by
  have h : interior A ∩ interior B ⊆ interior (A ∩ B) :=
    interior_inter_interior_subset_interior_inter (X := X) (A := A) (B := B)
  exact closure_mono h