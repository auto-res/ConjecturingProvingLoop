

theorem Topology.closure_union_three_eq {X : Type*} [TopologicalSpace X]
    (A B C : Set X) :
    closure (A ∪ B ∪ C) = closure A ∪ closure B ∪ closure C := by
  classical
  -- Apply the binary union lemma to `(A ∪ B)` and `C`.
  have h₁ : closure ((A ∪ B) ∪ C) =
      closure (A ∪ B) ∪ closure C :=
    Topology.closure_union_eq (A := A ∪ B) (B := C)
  -- Rewrite `closure (A ∪ B)` using the same lemma.
  have h₂ : closure (A ∪ B) = closure A ∪ closure B :=
    Topology.closure_union_eq (A := A) (B := B)
  -- Assemble the pieces and tidy up associativity of `∪`.
  simpa [h₂, Set.union_assoc] using h₁