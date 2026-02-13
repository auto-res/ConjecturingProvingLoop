

theorem denseInterior_prod_of_denseInterior_left_and_denseInterior_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hA : Dense (interior A)) (hB : Dense (interior B)) :
    Dense (interior (A ×ˢ B)) := by
  -- Characterize density through closure.
  have hA_closure : closure (interior A : Set X) = (Set.univ : Set X) := by
    simpa using hA.closure_eq
  have hB_closure : closure (interior B : Set Y) = (Set.univ : Set Y) := by
    simpa using hB.closure_eq
  -- Rewrite the closure of the interior of the product.
  have h_int_prod :
      interior (A ×ˢ B) = interior A ×ˢ interior B := by
    simpa using interior_prod_eq (s := A) (t := B)
  have h_closure_prod :
      closure (interior (A ×ˢ B) : Set (X × Y)) =
        closure (interior A) ×ˢ closure (interior B) := by
    simpa [h_int_prod] using
      (closure_prod_eq (s := interior A) (t := interior B))
  -- Combine the above to obtain that the closure is the whole space.
  have h_closure_eq_univ :
      closure (interior (A ×ˢ B) : Set (X × Y)) =
        (Set.univ : Set (X × Y)) := by
    simpa [hA_closure, hB_closure, Set.univ_prod_univ] using h_closure_prod
  -- Conclude density from the closure characterization.
  exact (dense_iff_closure_eq).2 h_closure_eq_univ