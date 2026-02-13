

theorem interior_subset_interiorClosureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure (interior A)) := by
  -- First, `interior A` is contained in `closure (interior A)`.
  have h₁ : interior A ⊆ closure (interior A) := subset_closure
  -- Applying `interior` to both sides (and using monotonicity) yields the result.
  have h₂ : interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono h₁
  simpa [interior_interior] using h₂