

theorem Topology.P1_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 C → Topology.P1 (A ∪ B ∪ C) := by
  intro hA hB hC
  -- First, combine `A` and `B`.
  have hAB : Topology.P1 (A ∪ B) := Topology.P1_union (A := A) (B := B) hA hB
  -- Then, unite the result with `C`.
  have hABC : Topology.P1 ((A ∪ B) ∪ C) :=
    Topology.P1_union (A := A ∪ B) (B := C) hAB hC
  -- Reassociate unions to match the desired form.
  simpa [Set.union_assoc] using hABC