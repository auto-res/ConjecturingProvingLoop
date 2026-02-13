

theorem P2_iff_P3_of_open {A : Set X} (hA : IsOpen A) : P2 A ↔ P3 A := by
  dsimp [P2, P3]
  simpa [hA.interior_eq]

theorem exists_open_subset_P2 {A : Set X} : ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ P2 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_, ?_⟩
  · intro x hx
    trivial
  · dsimp [P2]
    simp [interior_univ, closure_univ]

theorem P1_union {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  dsimp [P1] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hx' : x ∈ closure (interior A) := hA hxA
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact hsubset hx'
  | inr hxB =>
      have hx' : x ∈ closure (interior B) := hB hxB
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact hsubset hx'