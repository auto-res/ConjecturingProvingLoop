

theorem Topology.P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 C → Topology.P2 (A ∪ B ∪ C) := by
  intro hA hB hC
  -- First, unite `A` and `B`.
  have hAB : Topology.P2 (A ∪ B) := Topology.P2_union (A := A) (B := B) hA hB
  -- Then unite the result with `C`.
  have hABC : Topology.P2 ((A ∪ B) ∪ C) :=
    Topology.P2_union (A := A ∪ B) (B := C) hAB hC
  -- Reassociate unions to match the desired form.
  simpa [Set.union_assoc] using hABC