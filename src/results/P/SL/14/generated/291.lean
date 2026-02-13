

theorem Topology.interiorClosure_union_three_eq
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    interior (closure (A ∪ B ∪ C : Set X)) =
      interior (closure (A : Set X) ∪ closure B ∪ closure C) := by
  -- First, rewrite using the two–set union lemma with the block `(A ∪ B)` and `C`.
  have h₁ :
      interior (closure ((A ∪ B) ∪ C : Set X)) =
        interior (closure (A ∪ B : Set X) ∪ closure C) := by
    simpa using
      (Topology.interiorClosure_union_eq (X := X) (A := A ∪ B) (B := C))
  -- Next, rewrite `interior (closure (A ∪ B))` using the same lemma for `A` and `B`.
  have h₂ :
      interior (closure (A ∪ B : Set X)) =
        interior (closure (A : Set X) ∪ closure B) := by
    simpa using
      (Topology.interiorClosure_union_eq (X := X) (A := A) (B := B))
  -- Combine the two equalities and simplify with associativity of `∪`.
  simpa [Set.union_assoc, h₂] using h₁