

theorem Topology.interior_inter_eq_self_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∩ B : Set X) = A ∩ B := by
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  simpa using hOpen.interior_eq