

theorem Topology.interior_closure_union_three_eq {X : Type*} [TopologicalSpace X]
    (A B C : Set X) :
    interior (closure (A ∪ B ∪ C : Set X)) =
      interior (closure A ∪ closure B ∪ closure C) := by
  -- Reassociate the union to fit the binary lemmas.
  have h₁ : (A ∪ B ∪ C : Set X) = (A ∪ B) ∪ C := by
    simpa [Set.union_assoc]
  -- Use the two–set lemma for closures.
  have h₂ : (closure (A ∪ B) : Set X) = closure A ∪ closure B :=
    Topology.closure_union_eq (A := A) (B := B)
  -- Apply the binary lemma twice, rewriting along the way.
  calc
    interior (closure (A ∪ B ∪ C : Set X))
        = interior (closure ((A ∪ B) ∪ C)) := by
          simpa [h₁]
    _ = interior (closure (A ∪ B) ∪ closure C) := by
          simpa using
            (Topology.interior_closure_union_eq (A := A ∪ B) (B := C))
    _ = interior ((closure A ∪ closure B) ∪ closure C) := by
          simpa [h₂]
    _ = interior (closure A ∪ closure B ∪ closure C) := by
          simpa [Set.union_assoc]