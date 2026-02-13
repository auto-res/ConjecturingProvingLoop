

theorem Topology.P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B) :
    Topology.P1 (X := X) (closure (A ∪ B : Set X)) := by
  -- First, `P1` holds for the union `A ∪ B`.
  have hUnion : Topology.P1 (X := X) (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  -- Then, upgrade the property to the closure of the union.
  exact
    Topology.P1_closure_of_P1 (X := X) (A := A ∪ B) hUnion