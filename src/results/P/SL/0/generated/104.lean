

theorem P1_closure_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 C →
      Topology.P1 (closure ((A ∪ B ∪ C) : Set X)) := by
  intro hA hB hC
  -- First, `P1` for the triple union.
  have hUnion : Topology.P1 (A ∪ B ∪ C) :=
    Topology.P1_union_three (X := X) (A := A) (B := B) (C := C) hA hB hC
  -- Taking the closure preserves `P1`.
  have hClosure : Topology.P1 (closure ((A ∪ B ∪ C) : Set X)) :=
    Topology.P1_implies_P1_closure (X := X) (A := A ∪ B ∪ C) hUnion
  simpa using hClosure