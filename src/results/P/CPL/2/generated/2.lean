

theorem P3_of_P2 {A : Set X} (h : P2 A) : P3 A := by
  -- unfold the definitions of `P2` and `P3`
  unfold P2 at h
  unfold P3
  -- combine the two inclusions
  exact subset_trans h (interior_mono (closure_mono interior_subset))

theorem P3_union {A B : Set X} (hA : P3 A) (hB : P3 B) : P3 (A ∪ B) := by
  classical
  unfold P3 at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hx1 : x ∈ interior (closure A) := hA hxA
      have h_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure A ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact h_subset hx1
  | inr hxB =>
      have hx1 : x ∈ interior (closure B) := hB hxB
      have h_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure B ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inr hy
        exact this
      exact h_subset hx1

theorem P2_interior (A : Set X) : P2 (interior A) := by
  unfold P2
  simpa [interior_interior] using
    (interior_maximal (subset_closure) isOpen_interior :
      (interior A : Set X) ⊆ interior (closure (interior A)))

theorem exists_nonempty_P3 [Nonempty X] : ∃ A : Set X, A.Nonempty ∧ P3 A := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty X›
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · exact ⟨x₀, by simp⟩
  · simpa using (P3_univ : P3 (Set.univ : Set X))

theorem P2_iff_P1_and_P3 {A : Set X} : P2 A ↔ P1 A ∧ P3 A := by
  constructor
  · intro h
    exact ⟨P1_of_P2 h, P3_of_P2 h⟩
  · rintro ⟨hP1, hP3⟩
    have h_cl : closure (interior A) = closure A :=
      (P1_iff_closure_interior_subset).1 hP1
    simpa [P2, h_cl] using hP3

theorem P3_of_dense {A : Set X} (hA : Dense A) : P3 A := by
  unfold P3
  simpa [hA.closure_eq, interior_univ] using
    (Set.subset_univ (A : Set X))