

theorem dense_implies_dense_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Dense (interior (closure A)) := by
  intro hDense
  -- From the density of `A` we know that `closure (interior (closure A)) = univ`.
  have h_closure_eq :
      closure (interior (closure A) : Set X) = (Set.univ : Set X) :=
    dense_closure_interior_closure_eq_univ (X := X) (A := A) hDense
  -- Translate this equality into density.
  exact (dense_iff_closure_eq).2 h_closure_eq