

theorem Topology.interior_inter_eq_interiors_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∩ B) = interior A ∩ interior B := by
  -- Since `A` and `B` are open, so is `A ∩ B`, and its interior is itself.
  have hInt : interior (A ∩ B) = A ∩ B :=
    (hA.inter hB).interior_eq
  -- The interior of an open set is the set itself.
  have hA_int : interior A = A := hA.interior_eq
  have hB_int : interior B = B := hB.interior_eq
  -- Substitute and simplify.
  simpa [hInt, hA_int, hB_int]