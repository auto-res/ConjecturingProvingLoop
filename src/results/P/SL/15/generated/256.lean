

theorem dense_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Dense (closure A) := by
  intro hDense
  -- The closure of a dense set is the whole space,
  -- hence its closure (taken once more) is also the whole space.
  have h_closure :
      closure (closure A : Set X) = (Set.univ : Set X) := by
    simpa [hDense.closure_eq, closure_univ, closure_closure]
  -- Translate this equality into the desired density statement.
  exact (dense_iff_closure_eq (s := closure A)).2 h_closure