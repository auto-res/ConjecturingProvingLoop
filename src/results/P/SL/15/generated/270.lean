

theorem interior_closure_prod_of_dense_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hDense : Dense B) :
    interior (closure (A ×ˢ B)) =
      interior (closure A) ×ˢ (Set.univ : Set Y) := by
  -- Start from the general description of the left‐hand side.
  have hProd :=
    interior_closure_prod (X := X) (Y := Y) (A := A) (B := B)
  -- A dense set has the whole space as its closure.
  have hClosureB : closure (B : Set Y) = (Set.univ : Set Y) := by
    simpa using hDense.closure_eq
  -- Therefore its interior is also the whole space.
  have hIntClosureB : interior (closure (B : Set Y)) = (Set.univ : Set Y) := by
    have : interior (closure (B : Set Y)) = interior ((Set.univ : Set Y)) := by
      simpa [hClosureB]
    simpa [interior_univ] using this
  -- Substitute into the original equality.
  simpa [hIntClosureB] using hProd