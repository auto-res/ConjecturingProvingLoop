

theorem Topology.P1_union_interior {X : Type*} [TopologicalSpace X] (A B : Set X) :
    Topology.P1 (X := X) (interior A ∪ interior B) := by
  -- `P1` holds for the interior of any set.
  have hA : Topology.P1 (X := X) (interior A) :=
    Topology.P1_interior (X := X) (A := A)
  have hB : Topology.P1 (X := X) (interior B) :=
    Topology.P1_interior (X := X) (A := B)
  -- Combine the two `P1` properties using the union lemma.
  simpa using
    Topology.P1_union (X := X) (A := interior A) (B := interior B) hA hB