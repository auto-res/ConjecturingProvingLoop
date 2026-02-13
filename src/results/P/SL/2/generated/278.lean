

theorem Topology.interior_diff_isClosed_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    IsClosed (B : Set X) → interior (A \ B : Set X) = interior A \ B := by
  intro hClosed
  -- The complement of a closed set is open.
  have hOpen : IsOpen ((B : Set X)ᶜ) := hClosed.isOpen_compl
  -- Apply the lemma for an intersection with an open (right) set to `A ∩ Bᶜ`.
  have h :=
    Topology.interior_inter_isOpen_right (A := A) (B := (Bᶜ)) hOpen
  -- Rewrite intersections with set difference.
  simpa [Set.diff_eq] using h