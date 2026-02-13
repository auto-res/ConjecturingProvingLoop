

theorem P1_sdiff_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P1 (Aᶜ) := by
  have h_open : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hA
  exact P1_of_open (A := Aᶜ) h_open

theorem exists_P3_subset_closed {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ C, IsClosed C ∧ C ⊆ A ∧ P3 C := by
  refine ⟨(∅ : Set X), isClosed_empty, Set.empty_subset _, ?_⟩
  exact P3_empty (X := X)