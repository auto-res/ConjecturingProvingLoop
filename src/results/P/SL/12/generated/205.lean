

theorem Topology.P3_union_interior_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : Topology.P3 (X := X) A) :
    Topology.P3 (X := X) (A ∪ interior B) := by
  -- `P3` holds for `interior B` because it is an open set.
  have hB : Topology.P3 (X := X) (interior B) :=
    Topology.P3_interior (X := X) (A := B)
  -- Combine the two `P3` properties via the existing union lemma.
  exact Topology.P3_union (X := X) (A := A) (B := interior B) hA hB