

theorem Topology.closureInterior_inter_eq_closure_inter_of_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∩ B)) = closure (A ∩ B) := by
  -- The intersection of two open sets is open.
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  -- For an open set, its interior is itself.
  have hInt : interior (A ∩ B) = A ∩ B := hOpen.interior_eq
  -- Substitute and simplify.
  simpa [hInt]