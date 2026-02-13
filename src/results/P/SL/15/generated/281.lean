

theorem dense_left_implies_dense_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Dense A → Dense (A ∪ B) := by
  intro hDenseA
  -- `A` is dense, so its closure is the whole space.
  have hClosureA : closure (A : Set X) = (Set.univ : Set X) := by
    simpa using hDenseA.closure_eq
  -- The inclusion `A ⊆ A ∪ B` yields an inclusion of closures.
  have hSubset : closure (A : Set X) ⊆ closure (A ∪ B) :=
    closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
  -- Hence `closure (A ∪ B)` contains every point of the space.
  have hUnivSubset : (Set.univ : Set X) ⊆ closure (A ∪ B) := by
    simpa [hClosureA] using hSubset
  -- Combine the inclusions to obtain the equality of sets.
  have hClosureUnion : closure (A ∪ B : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro x _; trivial
    · exact hUnivSubset
  -- Translate the closure equality into the desired density statement.
  exact (dense_iff_closure_eq (s := A ∪ B)).2 hClosureUnion