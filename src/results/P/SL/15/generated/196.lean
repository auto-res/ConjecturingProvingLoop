

theorem dense_prod_of_dense_left_and_dense_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : Dense A) (hB : Dense B) :
    Dense (A ×ˢ B) := by
  -- We show that the closure of `A ×ˢ B` is the whole space.
  have hClosure :
      closure (A ×ˢ B : Set (X × Y)) = (Set.univ : Set (X × Y)) := by
    calc
      closure (A ×ˢ B : Set (X × Y))
          = closure A ×ˢ closure B := by
            simpa using closure_prod_eq (s := A) (t := B)
      _ = (Set.univ : Set X) ×ˢ (Set.univ : Set Y) := by
        simpa [hA.closure_eq, hB.closure_eq]
      _ = (Set.univ : Set (X × Y)) := by
        simpa [Set.univ_prod_univ]
  -- Conclude density from the characterization via closures.
  exact (dense_iff_closure_eq).2 hClosure