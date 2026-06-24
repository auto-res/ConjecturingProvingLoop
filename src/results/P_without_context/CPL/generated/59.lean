

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hP2
  exact hP2.trans interior_subset

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  dsimp [P2]
  simpa [interior_interior] using
    (interior_mono (subset_closure : interior A ⊆ closure (interior A)))

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hA hB
  dsimp [P1] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_cl : x ∈ closure (interior A) := hA hxA
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (by
          intro y hy
          exact Or.inl hy))
      exact h_subset hx_cl
  | inr hxB =>
      have hx_cl : x ∈ closure (interior B) := hB hxB
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (by
          intro y hy
          exact Or.inr hy))
      exact h_subset hx_cl

theorem exists_dense_subset_satisfying_P2 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, Dense A ∧ P2 A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · -- `univ` is dense
    have : closure (Set.univ : Set X) = (Set.univ : Set X) := by
      simp
    simpa [Dense] using this
  · -- `P2` holds for `univ`
    dsimp [P2]
    intro x hx
    simpa [interior_univ, closure_univ] using hx