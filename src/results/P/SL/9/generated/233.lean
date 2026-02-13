

theorem Topology.closure_union_four_eq {X : Type*} [TopologicalSpace X]
    (A B C D : Set X) :
    closure (A ∪ B ∪ C ∪ D) =
      closure A ∪ closure B ∪ closure C ∪ closure D := by
  classical
  -- Regroup to apply the binary union lemma.
  have h₁ : (A ∪ B ∪ C ∪ D : Set X) = ((A ∪ B ∪ C) ∪ D) := by
    simpa [Set.union_assoc]
  -- Use the three–set lemma for the inner union.
  have h₂ :
      closure (A ∪ B ∪ C) = closure A ∪ closure B ∪ closure C :=
    Topology.closure_union_three_eq (A := A) (B := B) (C := C)
  calc
    closure (A ∪ B ∪ C ∪ D)
        = closure ((A ∪ B ∪ C) ∪ D) := by
          simpa [h₁]
    _ = closure (A ∪ B ∪ C) ∪ closure D := by
          simpa using
            (Topology.closure_union_eq (A := A ∪ B ∪ C) (B := D))
    _ = (closure A ∪ closure B ∪ closure C) ∪ closure D := by
          simpa [h₂]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D := by
          simpa [Set.union_assoc, Set.union_left_comm, Set.union_comm]