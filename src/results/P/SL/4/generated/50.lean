

theorem interior_closure_interior_closure_subset_interior_closure {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure A))) ⊆ interior (closure A) := by
  -- First note: `interior (closure A)` is contained in `closure A`.
  have h₁ : interior (closure A) ⊆ closure A := interior_subset
  -- Taking closures preserves inclusions.
  have h₂ : closure (interior (closure A)) ⊆ closure (closure A) :=
    closure_mono h₁
  -- Simplify `closure (closure A)` to `closure A`.
  have h₂' : closure (interior (closure A)) ⊆ closure A := by
    simpa [closure_closure] using h₂
  -- Taking interiors preserves inclusions, giving the desired result.
  exact interior_mono h₂'