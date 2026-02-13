

theorem Topology.P1_union_open_right {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hA : Topology.P1 (X := X) A) (hU : IsOpen (U : Set X)) :
    Topology.P1 (X := X) (A ∪ U) := by
  -- `P1` holds for the open set `U`.
  have hU_P1 : Topology.P1 (X := X) U :=
    Topology.isOpen_P1 (X := X) (A := U) hU
  -- Combine the two `P1` properties via the union lemma.
  exact Topology.P1_union (X := X) (A := A) (B := U) hA hU_P1