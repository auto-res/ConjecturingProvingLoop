

theorem frontier_eq_closure_inter_compl_of_open
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    frontier A = closure A ∩ Aᶜ := by
  -- Start from the general characterization
  -- `frontier A = closure A ∩ (interior A)ᶜ`.
  have h :=
    frontier_eq_closure_inter_compl_interior (X := X) (A := A)
  -- For an open set `A` we have `interior A = A`, so the right‐hand side
  -- simplifies to `closure A ∩ Aᶜ`.
  simpa [hA.interior_eq] using h