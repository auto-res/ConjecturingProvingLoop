

theorem P1_union_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 (X:=X) A) : Topology.P1 (X:=X) (A ∪ interior A) := by
  simpa using
    P1_union (A := A) (B := interior A) hA (P1_interior (A := A))