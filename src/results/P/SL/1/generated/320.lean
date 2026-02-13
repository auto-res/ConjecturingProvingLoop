

theorem Topology.interior_inter_eq_inter_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∩ B) = interior A ∩ interior B := by
  calc
    interior (A ∩ B) = A ∩ B := (hA.inter hB).interior_eq
    _ = interior A ∩ interior B := by
      simpa [hA.interior_eq, hB.interior_eq]