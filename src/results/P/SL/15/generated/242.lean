

theorem denseInterior_implies_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Dense A := by
  intro hDenseInt
  -- From the density of `interior A` we know `closure A = univ`.
  have h_closure_eq : closure A = (Set.univ : Set X) :=
    denseInterior_implies_closure_eq_univ (X := X) (A := A) hDenseInt
  -- Translate the closure equality into density.
  exact (dense_iff_closure_eq (s := A)).2 h_closure_eq