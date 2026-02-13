

theorem Topology.interior_inter_three_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B C : Set X} (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) :
    interior (A ∩ B ∩ C) = A ∩ B ∩ C := by
  have hOpen : IsOpen (A ∩ B ∩ C) := (hA.inter hB).inter hC
  simpa using hOpen.interior_eq