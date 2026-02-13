

theorem interior_inter_of_open_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsOpen (B : Set X)) :
    interior (A ∩ B : Set X) = interior A ∩ B := by
  -- Apply the “left‐open” version to the swapped intersection.
  have h :=
    interior_inter_of_open_left (X := X) (A := B) (B := A) hB
  -- Rewrite using commutativity of `∩`.
  simpa [Set.inter_comm] using h