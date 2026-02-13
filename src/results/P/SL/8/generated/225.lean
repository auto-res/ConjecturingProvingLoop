

theorem closureInterior_diff_subset_closureInterior_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B)) ⊆ closure (interior A) := by
  -- The interior of a set difference is contained in the interior of the left set.
  have h : interior (A \ B) ⊆ interior A :=
    interior_diff_subset_left (X := X) (A := A) (B := B)
  -- Taking closures preserves inclusions.
  exact closure_mono h