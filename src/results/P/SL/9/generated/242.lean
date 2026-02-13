

theorem Topology.closure_union_five_eq {X : Type*} [TopologicalSpace X]
    (A B C D E : Set X) :
    closure (A ∪ B ∪ C ∪ D ∪ E) =
      closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E := by
  classical
  -- Reassociate the union to apply the binary union lemma.
  have h₁ : (A ∪ B ∪ C ∪ D ∪ E : Set X) = ((A ∪ B ∪ C ∪ D) ∪ E) := by
    simpa [Set.union_assoc]
  -- Use the four–set lemma for the inner union.
  have h₂ :
      closure (A ∪ B ∪ C ∪ D) =
        closure A ∪ closure B ∪ closure C ∪ closure D :=
    Topology.closure_union_four_eq (A := A) (B := B) (C := C) (D := D)
  -- Assemble the pieces.
  calc
    closure (A ∪ B ∪ C ∪ D ∪ E)
        = closure ((A ∪ B ∪ C ∪ D) ∪ E) := by
          simpa [h₁]
    _ = closure (A ∪ B ∪ C ∪ D) ∪ closure E := by
          simpa using
            (Topology.closure_union_eq (A := A ∪ B ∪ C ∪ D) (B := E))
    _ = (closure A ∪ closure B ∪ closure C ∪ closure D) ∪ closure E := by
          simpa [h₂]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E := by
          simp [Set.union_assoc, Set.union_left_comm, Set.union_comm]