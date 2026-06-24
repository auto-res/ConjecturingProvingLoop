

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 A) : Topology.P3 A := by
  dsimp [P2] at h
  dsimp [P3]
  intro x hxA
  have hx1 : x ∈ interior (closure (interior A)) := h hxA
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure : closure (interior A) ⊆ closure A := by
      exact closure_mono interior_subset
    exact interior_mono h_closure
  exact hsubset hx1

theorem closure_interior_eq_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P1 A) : closure (interior A) = closure A := by
  apply le_antisymm
  · exact closure_mono interior_subset
  ·
    have : closure A ⊆ closure (closure (interior A)) := closure_mono h
    simpa [closure_closure] using this

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (A ∪ B) := by
  -- Unfold the definition of `P1` for the hypotheses and the goal.
  dsimp [Topology.P1] at hA hB
  dsimp [Topology.P1]
  -- Take an arbitrary point in `A ∪ B`.
  intro x hx
  -- Analyse whether `x` comes from `A` or `B`.
  cases hx with
  | inl hxA =>
      -- Case `x ∈ A`
      have hxA_cl : x ∈ closure (interior A) := hA hxA
      -- `closure (interior A)` is contained in `closure (interior (A ∪ B))`
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        -- because `interior A ⊆ interior (A ∪ B)`
        have : interior A ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact hsubset hxA_cl
  | inr hxB =>
      -- Case `x ∈ B`
      have hxB_cl : x ∈ closure (interior B) := hB hxB
      -- `closure (interior B)` is contained in `closure (interior (A ∪ B))`
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        -- because `interior B ⊆ interior (A ∪ B)`
        have : interior B ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact this
      exact hsubset hxB_cl

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 A) : Topology.P1 A := by
  dsimp [Topology.P1, Topology.P2] at *
  intro x hxA
  have hx₁ : x ∈ interior (closure (interior A)) := h hxA
  have h_subset : interior (closure (interior A)) ⊆ closure (interior A) := by
    simpa using interior_subset
  exact h_subset hx₁