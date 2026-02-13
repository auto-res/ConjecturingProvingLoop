

theorem Topology.P2_interior_union_interior {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    Topology.P2 (X := X) (interior A ∪ interior B) := by
  -- `P2` holds for the interior of any set.
  have hA : Topology.P2 (X := X) (interior A) :=
    Topology.P2_interior (X := X) (A := A)
  have hB : Topology.P2 (X := X) (interior B) :=
    Topology.P2_interior (X := X) (A := B)
  -- Combine the two instances using the union lemma for `P2`.
  exact
    Topology.P2_union (X := X)
      (A := interior A) (B := interior B) hA hB