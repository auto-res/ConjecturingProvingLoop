

theorem dense_prod_univ_left_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty Y]
    {A : Set X} :
    Dense (A ×ˢ (Set.univ : Set Y)) ↔ Dense A := by
  constructor
  · intro hDenseProd
    exact
      dense_prod_univ_left_of_dense
        (X := X) (Y := Y) (A := A) hDenseProd
  · intro hDenseA
    -- `Set.univ` is dense in `Y`.
    have hDenseUniv : Dense (Set.univ : Set Y) := by
      have h_closure : closure (Set.univ : Set Y) = (Set.univ : Set Y) := by
        simpa [closure_univ]
      exact (dense_iff_closure_eq).2 h_closure
    -- Combine the densities of the factors.
    exact
      dense_prod_of_dense_left_and_dense_right
        (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y))
        hDenseA hDenseUniv