

theorem Topology.interior_inter_eq_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∩ B : Set X) = A ∩ B := by
  simpa using (IsOpen.inter hA hB).interior_eq