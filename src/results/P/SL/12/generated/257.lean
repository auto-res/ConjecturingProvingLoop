

theorem Topology.P1_union_open_left {X : Type*} [TopologicalSpace X] {U A : Set X}
    (hU : IsOpen (U : Set X)) (hA : Topology.P1 (X := X) A) :
    Topology.P1 (X := X) (U ∪ A) := by
  -- `P1` holds automatically for an open set.
  have hU_P1 : Topology.P1 (X := X) U :=
    Topology.isOpen_P1 (X := X) (A := U) hU
  -- Combine the two `P1` properties using the union lemma.
  simpa [Set.union_comm] using
    Topology.P1_union (X := X) (A := A) (B := U) hA hU_P1