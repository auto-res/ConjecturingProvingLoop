

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : P3 A := by
  -- First, show that `closure A = Set.univ`.
  have h_dense_closure : (closure (A : Set X)) = (Set.univ : Set X) := by
    -- `closure (interior A)` is all of `X` by hypothesis and is contained in `closure A`.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
      simpa [h] using
        (closure_mono (interior_subset : (interior A : Set X) ⊆ A))
    -- Trivially, `closure A ⊆ Set.univ`.
    have h_subset_univ : (closure (A : Set X)) ⊆ (Set.univ : Set X) := by
      intro x hx
      trivial
    exact le_antisymm h_subset_univ h_univ_subset
  -- With `closure A = Set.univ`, apply the existing lemma `P3_of_dense`.
  exact P3_of_dense (X := X) (A := A) h_dense_closure

theorem exists_open_between_interior_and_closure {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U, IsOpen U ∧ interior A ⊆ U ∧ U ⊆ closure A := by
  refine ⟨interior (closure (A : Set X)), isOpen_interior, ?_, ?_⟩
  ·
    have : (interior A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    simpa using this
  ·
    exact interior_subset