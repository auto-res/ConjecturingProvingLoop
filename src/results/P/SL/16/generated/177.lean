

theorem Topology.interior_inter_eq_of_open {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∩ B : Set X) = A ∩ B := by
  -- The intersection of two open sets is open.
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  -- For an open set, its interior is itself.
  simpa using hOpen.interior_eq