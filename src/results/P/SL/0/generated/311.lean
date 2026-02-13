

theorem P2_closure_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    Topology.P2 (closure (A : Set X)) →
    Topology.P2 (closure (B : Set X)) →
    Topology.P2 (closure (C : Set X)) →
    Topology.P2 (closure ((A ∪ B ∪ C) : Set X)) := by
  intro hA hB hC
  -- First, unite `closure A` and `closure B`.
  have hAB : Topology.P2 (closure ((A ∪ B) : Set X)) :=
    Topology.P2_closure_union (X := X) (A := A) (B := B) hA hB
  -- Next, unite the result with `closure C`.
  have hABC : Topology.P2 (closure (((A ∪ B) ∪ C) : Set X)) :=
    Topology.P2_closure_union (X := X) (A := A ∪ B) (B := C) hAB hC
  -- Reassociate unions to match the goal.
  simpa [Set.union_assoc] using hABC