

theorem Topology.interior_inter_open_right {X : Type*} [TopologicalSpace X]
    {A U : Set X} (hU : IsOpen U) :
    interior (A ∩ U) = interior A ∩ U := by
  have h :=
    Topology.interior_inter_open_left (X := X) (U := U) (A := A) hU
  simpa [Set.inter_comm] using h