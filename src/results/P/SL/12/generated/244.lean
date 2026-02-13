

theorem Topology.P1_union_interior_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : Topology.P1 (X := X) A) :
    Topology.P1 (X := X) (A ∪ interior B) := by
  -- `P1` holds for `interior B` because the interior of any set is open.
  have hB : Topology.P1 (X := X) (interior B) :=
    Topology.P1_interior (X := X) (A := B)
  -- Combine the two `P1` properties using the existing union lemma.
  simpa using
    Topology.P1_union (X := X) (A := A) (B := interior B) hA hB