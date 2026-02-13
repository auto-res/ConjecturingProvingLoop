

theorem P2_union₄ {X : Type*} [TopologicalSpace X] {A B C D : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) (hD : Topology.P2 D) : Topology.P2 (A ∪ B ∪ C ∪ D) := by
  -- First, combine `A`, `B`, and `C`
  have hABC : Topology.P2 (A ∪ B ∪ C) :=
    Topology.P2_union₃ hA hB hC
  -- Then add `D`
  have hABCD : Topology.P2 ((A ∪ B ∪ C) ∪ D) :=
    Topology.P2_union hABC hD
  -- Rewrite to the desired union of four sets
  simpa [Set.union_assoc] using hABCD