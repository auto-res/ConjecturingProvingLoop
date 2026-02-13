

theorem P1_closure_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 C → Topology.P1 D →
      Topology.P1 (closure (A ∪ B ∪ C ∪ D : Set X)) := by
  intro hA hB hC hD
  -- First, obtain `P1` for the four‐fold union.
  have hUnion : Topology.P1 (A ∪ B ∪ C ∪ D) :=
    Topology.P1_union_four (X := X) (A := A) (B := B) (C := C) (D := D) hA hB hC hD
  -- Taking the closure preserves `P1`.
  have hClosure : Topology.P1 (closure ((A ∪ B ∪ C ∪ D) : Set X)) :=
    Topology.P1_implies_P1_closure (X := X) (A := A ∪ B ∪ C ∪ D) hUnion
  -- Reassociate unions to match the goal statement.
  simpa [Set.union_assoc] using hClosure