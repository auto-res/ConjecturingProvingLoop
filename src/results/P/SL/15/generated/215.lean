

theorem dense_iff_dense_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A ↔ Dense (interior (closure A)) := by
  constructor
  · intro hDense
    exact
      dense_implies_dense_interior_closure (X := X) (A := A) hDense
  · intro hDenseInt
    exact
      denseInterior_closure_implies_dense (X := X) (A := A) hDenseInt