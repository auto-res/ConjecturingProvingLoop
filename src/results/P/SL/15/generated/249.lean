

theorem closure_interiors_union_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ interior B) ⊆ closure (interior (A ∪ B)) := by
  -- `interior A ∪ interior B` is contained in `interior (A ∪ B)`
  have h_subset : interior A ∪ interior B ⊆ interior (A ∪ B) :=
    interior_union (X := X) (A := A) (B := B)
  -- Taking closures preserves inclusion
  exact closure_mono h_subset