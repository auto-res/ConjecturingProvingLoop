

theorem P3_closure_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} :
    Topology.P3 (closure (A : Set X)) →
    Topology.P3 (closure (B : Set X)) →
    Topology.P3 (closure (C : Set X)) →
    Topology.P3 (closure (D : Set X)) →
    Topology.P3 (closure ((A ∪ B ∪ C ∪ D) : Set X)) := by
  intro hA hB hC hD
  -- First combine `A` and `B`.
  have hAB : Topology.P3 (closure ((A ∪ B) : Set X)) :=
    Topology.P3_closure_union (X := X) (A := A) (B := B) hA hB
  -- Next, add `C`.
  have hABC : Topology.P3 (closure (((A ∪ B) ∪ C) : Set X)) :=
    Topology.P3_closure_union (X := X) (A := A ∪ B) (B := C) hAB hC
  -- Finally, add `D`.
  have hABCD : Topology.P3 (closure ((((A ∪ B) ∪ C) ∪ D) : Set X)) :=
    Topology.P3_closure_union (X := X) (A := (A ∪ B) ∪ C) (B := D) hABC hD
  simpa [Set.union_assoc] using hABCD