

theorem dense_prod_univ_right_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    {B : Set Y} :
    Dense ((Set.univ : Set X) ×ˢ B) ↔ Dense B := by
  constructor
  · intro hDenseProd
    exact
      dense_prod_univ_right_of_dense
        (X := X) (Y := Y) (B := B) hDenseProd
  · intro hDenseB
    -- `univ` is trivially dense.
    have hDenseUniv : Dense (Set.univ : Set X) := by
      simpa [closure_univ] using
        (dense_iff_closure_eq (s := (Set.univ : Set X))).2 rfl
    -- Combine the densities of the two factors.
    simpa using
      dense_prod_of_dense_left_and_dense_right
        (X := X) (Y := Y)
        (A := (Set.univ : Set X)) (B := B) hDenseUniv hDenseB