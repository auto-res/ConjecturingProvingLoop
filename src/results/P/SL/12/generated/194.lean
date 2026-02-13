

theorem Topology.P2_union_interior_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 (X := X) A) :
    Topology.P2 (X := X) (A ∪ interior B) := by
  -- `P2` holds for `interior B` because it is an open set.
  have hB : Topology.P2 (X := X) (interior B) :=
    Topology.P2_interior (X := X) (A := B)
  -- Use the existing union lemma for `P2`.
  simpa using
    Topology.P2_union (X := X) (A := A) (B := interior B) hA hB