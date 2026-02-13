

theorem Topology.closure_union_six_eq {X : Type*} [TopologicalSpace X]
    (A B C D E F : Set X) :
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F) =
      closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪ closure F := by
  classical
  -- Regroup the big union so that we can apply the existing five-set lemma.
  have h₁ :
      (A ∪ B ∪ C ∪ D ∪ E ∪ F : Set X) = ((A ∪ B ∪ C ∪ D ∪ E) ∪ F) := by
    simp [Set.union_assoc]
  -- Apply the lemma for five sets to the regrouped part.
  have h₂ :
      closure (A ∪ B ∪ C ∪ D ∪ E) =
        closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E :=
    Topology.closure_union_five_eq (A := A) (B := B) (C := C) (D := D) (E := E)
  -- Put everything together.
  calc
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F) =
        closure ((A ∪ B ∪ C ∪ D ∪ E) ∪ F) := by
          simpa [h₁]
    _ = closure (A ∪ B ∪ C ∪ D ∪ E) ∪ closure F := by
          simpa using
            (Topology.closure_union_eq
                (A := A ∪ B ∪ C ∪ D ∪ E) (B := F))
    _ = (closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E) ∪
          closure F := by
          simpa [h₂]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
          closure F := by
          simp [Set.union_assoc, Set.union_left_comm, Set.union_comm]