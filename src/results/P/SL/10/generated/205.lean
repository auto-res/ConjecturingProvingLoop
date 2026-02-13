

theorem Topology.interior_inter_open_left_closure {X : Type*} [TopologicalSpace X]
    {U A : Set X} (hU : IsOpen U) :
    interior (U ∩ closure A) = U ∩ interior (closure A) := by
  simpa using
    (Topology.interior_inter_open_left (X := X) (U := U) (A := closure A) hU)