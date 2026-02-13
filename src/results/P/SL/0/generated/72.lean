

theorem P1_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 C → Topology.P1 (A ∪ B ∪ C) := by
  intro hA hB hC
  -- First, combine `A` and `B` using the existing two‐set union lemma.
  have hAB : Topology.P1 (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  -- Next, unite the result with `C`.
  have hABC : Topology.P1 ((A ∪ B) ∪ C) :=
    Topology.P1_union (X := X) (A := A ∪ B) (B := C) hAB hC
  -- Use associativity of `∪` to rewrite the goal.
  simpa [Set.union_assoc] using hABC