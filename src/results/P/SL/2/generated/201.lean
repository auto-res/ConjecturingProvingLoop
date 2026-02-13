

theorem Topology.interior_inter_isOpen_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsOpen B) :
    interior (A ∩ B : Set X) = interior A ∩ B := by
  simpa [Set.inter_comm] using
    (Topology.interior_inter_isOpen_left (A := B) (B := A) hB)