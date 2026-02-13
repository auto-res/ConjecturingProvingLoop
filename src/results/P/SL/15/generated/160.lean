

theorem closure_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure A)) ⊆ closure A := by
  -- `interior (closure A)` is contained in `closure A`
  have h_sub : interior (closure A) ⊆ closure A := interior_subset
  -- Taking closures preserves inclusion
  have h_closure : closure (interior (closure A)) ⊆ closure (closure A) :=
    closure_mono h_sub
  -- Simplify `closure (closure A)` to `closure A`
  simpa [closure_closure] using h_closure