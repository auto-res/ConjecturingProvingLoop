

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B) := by
  classical
  unfold P2 at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hx₁ : x ∈ interior (closure (interior A)) := hA hxA
      -- use monotonicity `interior ⊆ interior` via `A ⊆ A ∪ B`
      have h_sub :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        have h_closure_subset :
            closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          have h_int_subset : interior A ⊆ interior (A ∪ B) := by
            apply interior_mono
            intro y hy
            exact Or.inl hy
          exact h_int_subset
        exact h_closure_subset
      exact h_sub hx₁
  | inr hxB =>
      -- `x ∈ B`
      have hx₁ : x ∈ interior (closure (interior B)) := hB hxB
      have h_sub :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        have h_closure_subset :
            closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          have h_int_subset : interior B ⊆ interior (A ∪ B) := by
            apply interior_mono
            intro y hy
            exact Or.inr hy
          exact h_int_subset
        exact h_closure_subset
      exact h_sub hx₁

theorem exists_nontrivial_P1 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, A.Nonempty ∧ P1 A := by
  classical
  -- pick the whole space as our set
  rcases ‹Nonempty X› with ⟨x₀⟩
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · exact ⟨x₀, by simp⟩
  ·
    unfold P1
    simp

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (h : P1 A) : P1 (e '' A) := by
  classical
  unfold P1 at h ⊢
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` lies in the closure of the interior of `A`
  have hx : x ∈ closure (interior A) := h hxA
  -- transport this fact through the homeomorphism
  have h1 : e x ∈ closure (e '' interior A) := by
    -- first note that `e x` is in the image of the closure
    have : e x ∈ (e '' closure (interior A) : Set _) := ⟨x, hx, rfl⟩
    -- rewrite the image of the closure
    have h_eq : (e '' closure (interior A) : Set _) = closure (e '' interior A) := by
      simpa using e.image_closure (s := interior A)
    simpa [h_eq] using this
  -- identify `e '' interior A` with `interior (e '' A)`
  have h2 : e x ∈ closure (interior (e '' A)) := by
    have h_eq : (e '' interior A : Set _) = interior (e '' A) := by
      simpa using e.image_interior (s := A)
    simpa [h_eq] using h1
  exact h2

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (h : P3 A) : P3 (e '' A) := by
  classical
  unfold P3 at h ⊢
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  have hx : x ∈ interior (closure A) := h hxA
  have hx1 : e x ∈ interior (e '' closure A) := by
    have : e x ∈ (e '' interior (closure A) : Set _) := ⟨x, hx, rfl⟩
    have h_eq : (e '' interior (closure A) : Set _) = interior (e '' closure A) := by
      simpa using e.image_interior (s := closure A)
    simpa [h_eq] using this
  have h_eq : (e '' closure A : Set _) = closure (e '' A) := by
    simpa using e.image_closure (s := A)
  simpa [h_eq] using hx1