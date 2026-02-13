

theorem P1_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 C → Topology.P1 D →
      Topology.P1 (A ∪ B ∪ C ∪ D) := by
  intro hA hB hC hD
  -- First, unite `A`, `B`, and `C`.
  have hABC : Topology.P1 (A ∪ B ∪ C) :=
    Topology.P1_union_three (X := X) (A := A) (B := B) (C := C) hA hB hC
  -- Next, union the result with `D`.
  have hABCD : Topology.P1 ((A ∪ B ∪ C) ∪ D) :=
    Topology.P1_union (X := X) (A := A ∪ B ∪ C) (B := D) hABC hD
  -- Reassociate unions to match the goal.
  simpa [Set.union_assoc] using hABCD