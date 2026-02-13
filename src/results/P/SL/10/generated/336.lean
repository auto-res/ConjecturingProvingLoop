

theorem Topology.interior_inter_interior_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (interior A ∩ interior B) = interior A ∩ interior B := by
  -- `interior A` is open, so we may apply `interior_inter_open_left`.
  have h_open : IsOpen (interior A) := isOpen_interior
  have h :=
    Topology.interior_inter_open_left
      (X := X) (U := interior A) (A := interior B) h_open
  -- Simplify `interior (interior B)` to `interior B`.
  simpa [interior_interior] using h