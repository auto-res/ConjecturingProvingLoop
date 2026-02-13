

theorem closure_interior_closure_eq_closure_of_open {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    closure (interior (closure A)) = closure A := by
  apply subset_antisymm
  ·
    exact closure_interior_closure_subset_closure (X := X) (A := A)
  ·
    -- Since `A` is open, we have `A ⊆ interior (closure A)`.
    have h_sub : (A : Set X) ⊆ interior (closure A) := by
      have hIntSubset : interior A ⊆ interior (closure A) :=
        interior_mono subset_closure
      simpa [hA.interior_eq] using hIntSubset
    -- Taking closures preserves inclusions.
    exact closure_mono h_sub