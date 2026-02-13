

theorem Topology.closureInterior_inter_eq_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    closure (interior (A ∩ B : Set X)) = closure (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B : Set X) := IsOpen.inter hA hB
  simpa [hOpen.interior_eq]