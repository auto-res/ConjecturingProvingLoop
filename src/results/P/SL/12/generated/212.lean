

theorem Topology.P2_union_interior_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : Topology.P2 (X := X) B) :
    Topology.P2 (X := X) (interior A ∪ B) := by
  -- Reuse the “right‐hand side” lemma with the arguments swapped.
  have h := Topology.P2_union_interior_right (X := X) (A := B) (B := A) hB
  simpa [Set.union_comm] using h