

theorem closure_interior_subset_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    closure (interior A) ⊆ closure B := by
  -- `interior A` is contained in `A`, hence in `B`.
  have h : interior A ⊆ B := fun x hx => hAB (interior_subset hx)
  -- Taking closures preserves inclusions.
  exact closure_mono h