

theorem interior_closure_prod_of_dense_left
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hDense : Dense A) :
    interior (closure (A ×ˢ B)) =
      (Set.univ : Set X) ×ˢ interior (closure B) := by
  -- Express the interior of the closure of the product.
  have hProd :
      interior (closure (A ×ˢ B)) =
        interior (closure (A : Set X)) ×ˢ interior (closure B) :=
    interior_closure_prod (X := X) (Y := Y) (A := A) (B := B)
  -- Since `A` is dense, its closure is the whole space.
  have hClosureA : closure (A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Hence the interior of this closure is also the whole space.
  have hIntClosureA : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    have : interior (closure (A : Set X)) = interior ((Set.univ : Set X)) := by
      simpa [hClosureA]
    simpa [interior_univ] using this
  -- Substitute and simplify.
  simpa [hIntClosureA] using hProd