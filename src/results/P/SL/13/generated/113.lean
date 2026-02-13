

theorem Topology.P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B) :
    Topology.P1 (X := X) (closure ((A ∪ B) : Set X)) := by
  -- First, `P1` holds for the union `A ∪ B`.
  have h_union : Topology.P1 (X := X) (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  -- Then, `P1` is inherited by the closure of any set that satisfies `P1`.
  exact Topology.P1_implies_P1_closure (X := X) (A := A ∪ B) h_union