

theorem Topology.P3_union_open_right {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hA : Topology.P3 (X := X) A) (hU : IsOpen (U : Set X)) :
    Topology.P3 (X := X) (A ∪ U) := by
  -- `P3` holds for the open set `U`.
  have hU_P3 : Topology.P3 (X := X) U :=
    Topology.isOpen_P3 (X := X) (A := U) hU
  -- Combine the two `P3` properties via the union lemma.
  simpa using
    Topology.P3_union (X := X) (A := A) (B := U) hA hU_P3