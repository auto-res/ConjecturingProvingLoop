

theorem Topology.closureInterior_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B : Set X)) ⊆ closure (interior A) := by
  -- `interior (A \ B)` is contained in `interior A`.
  have h_sub :
      (interior (A \ B : Set X) : Set X) ⊆ interior A :=
    Topology.interior_diff_subset (X := X) (A := A) (B := B)
  -- Taking closures preserves inclusions.
  exact closure_mono h_sub