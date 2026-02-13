

theorem P3_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 C → Topology.P3 D →
    Topology.P3 (A ∪ B ∪ C ∪ D) := by
  intro hA hB hC hD
  -- Unite `A` and `B`.
  have hAB : Topology.P3 (A ∪ B) :=
    Topology.P3_union (X := X) (A := A) (B := B) hA hB
  -- Unite the result with `C`.
  have hABC : Topology.P3 ((A ∪ B) ∪ C) :=
    Topology.P3_union (X := X) (A := A ∪ B) (B := C) hAB hC
  -- Finally, unite with `D`.
  have hABCD : Topology.P3 (((A ∪ B) ∪ C) ∪ D) :=
    Topology.P3_union (X := X) (A := (A ∪ B) ∪ C) (B := D) hABC hD
  -- Reassociate unions to match the goal.
  simpa [Set.union_assoc] using hABCD