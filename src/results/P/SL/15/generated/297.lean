

theorem denseInterior_implies_dense_interior_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Dense (interior (closure (interior A))) := by
  intro hDense
  -- First, identify `interior (closure (interior A))` with `univ`.
  have h_eq :
      interior (closure (interior A)) = (Set.univ : Set X) :=
    interior_closure_interior_eq_univ_of_dense (X := X) (A := A) hDense
  -- The closure of `univ` is `univ`, so the closure of our set is `univ`.
  have h_closure :
      (closure (interior (closure (interior A)) : Set X)) =
        (Set.univ : Set X) := by
    simpa [h_eq, closure_univ]
  -- Conclude density from the characterisation via closures.
  exact
    (dense_iff_closure_eq
        (s := interior (closure (interior A)))).2 h_closure