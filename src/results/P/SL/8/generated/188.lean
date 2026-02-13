

theorem closureInterior_inter_eq_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∩ B)) = closure (A ∩ B) := by
  -- Since `A` and `B` are open, so is their intersection.
  have h_open : IsOpen (A ∩ B) := IsOpen.inter hA hB
  -- The interior of an open set is itself.
  have h_int : interior (A ∩ B) = A ∩ B := by
    simpa using h_open.interior_eq
  -- Rewrite using `h_int`.
  simpa [h_int]