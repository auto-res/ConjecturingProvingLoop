

theorem Topology.interior_inter_interior_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior ((A ∩ interior (B : Set X)) : Set X) = interior A ∩ interior B := by
  -- `interior B` is an open set.
  have h_open : IsOpen (interior (B : Set X)) := isOpen_interior
  -- Apply the general lemma for the intersection with an open set.
  simpa using
    Topology.interior_inter_open_right
      (X := X) (A := A) (B := interior (B : Set X)) h_open