

theorem Topology.interior_inter_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∩ B) = A ∩ B := by
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  simpa [hOpen.interior_eq]