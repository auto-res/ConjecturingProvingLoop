

theorem Topology.P3_interior_union_interior {X : Type*} [TopologicalSpace X] (A B : Set X) :
    Topology.P3 (X := X) (interior A ∪ interior B) := by
  -- `P3` holds for the interior of any set.
  have hA : Topology.P3 (X := X) (interior A) :=
    Topology.P3_interior (X := X) (A := A)
  have hB : Topology.P3 (X := X) (interior B) :=
    Topology.P3_interior (X := X) (A := B)
  -- Combine the two `P3` properties using the union lemma.
  exact
    Topology.P3_union (X := X)
      (A := interior A) (B := interior B) hA hB