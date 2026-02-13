

theorem dense_union_of_dense_left_and_dense_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense A → Dense B → Dense (A ∪ B) := by
  intro hA hB
  have hA_closure : closure A = (Set.univ : Set X) := by
    simpa using hA.closure_eq
  have hB_closure : closure B = (Set.univ : Set X) := by
    simpa using hB.closure_eq
  -- Any point of the space belongs to `closure A`, hence to `closure (A ∪ B)`.
  have h_subset : (Set.univ : Set X) ⊆ closure (A ∪ B) := by
    have h_incl : closure A ⊆ closure (A ∪ B) :=
      closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
    simpa [hA_closure] using h_incl
  -- Consequently, `closure (A ∪ B)` is the whole space.
  have h_closure_union : closure (A ∪ B) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro x _; trivial
    · exact h_subset
  -- Translate the closure equality into density.
  exact (dense_iff_closure_eq (s := A ∪ B)).2 h_closure_union