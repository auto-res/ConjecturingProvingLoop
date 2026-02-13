

theorem interior_subset_closureInteriorClosureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior (closure (interior A))) := by
  intro x hx
  -- `interior A ⊆ closure (interior A)`
  have hxCl : (x : X) ∈ closure (interior A) := subset_closure hx
  -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`
  have hIncl :
      closure (interior A) ⊆ closure (interior (closure (interior A))) := by
    have h :=
      closure_interior_subset_closure_interior_closure
        (X := X) (A := interior A)
    simpa [interior_interior] using h
  exact hIncl hxCl