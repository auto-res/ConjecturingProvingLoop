

theorem P3_closure_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    Topology.P3 (closure (A : Set X)) →
    Topology.P3 (closure (B : Set X)) →
    Topology.P3 (closure (C : Set X)) →
    Topology.P3 (closure ((A ∪ B ∪ C) : Set X)) := by
  intro hA hB hC
  -- First, unite the closures of `A` and `B`.
  have hAB : Topology.P3 (closure ((A ∪ B) : Set X)) :=
    Topology.P3_closure_union (X := X) (A := A) (B := B) hA hB
  -- Next, unite the result with the closure of `C`.
  have hABC : Topology.P3 (closure (((A ∪ B) ∪ C) : Set X)) :=
    Topology.P3_closure_union (X := X) (A := A ∪ B) (B := C) hAB hC
  -- Reassociate unions to match the desired form.
  simpa [Set.union_assoc] using hABC