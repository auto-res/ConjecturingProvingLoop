

theorem nonempty_of_closure_interior_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior (A : Set X))).Nonempty → (A : Set X).Nonempty := by
  intro hClInt
  -- First, obtain a point in `interior A` using the previously proven equivalence.
  have hInt :
      (interior (A : Set X)).Nonempty :=
    ((Topology.closure_interior_nonempty_iff_interior_nonempty
        (X := X) (A := A))).1 hClInt
  -- Since `interior A ⊆ A`, this point also lies in `A`.
  rcases hInt with ⟨x, hxInt⟩
  exact ⟨x, interior_subset hxInt⟩