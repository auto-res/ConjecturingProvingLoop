

theorem Topology.interior_inter_interior_eq_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A ∩ interior B) = interior A ∩ interior B := by
  -- `interior B` is open, so we can apply the general lemma
  have hOpen : IsOpen (interior B) := isOpen_interior
  simpa [interior_interior] using
    (Topology.interior_inter_eq_inter_left_of_isOpen_right
      (A := A) (B := interior B) hOpen)