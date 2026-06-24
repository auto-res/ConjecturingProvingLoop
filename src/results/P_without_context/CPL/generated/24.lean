

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  exact hP2.trans (interior_mono (closure_mono interior_subset))

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hAx =>
      have hx₁ : x ∈ closure (interior A) := hA hAx
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact hsubset hx₁
  | inr hBx =>
      have hx₁ : x ∈ closure (interior B) := hB hBx
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact hsubset hx₁

theorem exists_open_subset_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P3 A) : ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ closure U = closure A := by
  -- Choose the open set `U = interior (closure A)`
  refine ⟨interior (closure A), isOpen_interior, h, ?_⟩
  -- We prove `closure U = closure A`
  have h₁ : closure (interior (closure A)) ⊆ closure A := by
    -- `interior (closure A)` is contained in `closure A`
    have hsub : interior (closure A) ⊆ closure A := by
      simpa using interior_subset
    -- Take closures on both sides
    have hcl : closure (interior (closure A)) ⊆ closure (closure A) :=
      closure_mono hsub
    -- `closure (closure A)` is just `closure A`
    simpa [closure_closure] using hcl
  have h₂ : closure A ⊆ closure (interior (closure A)) := by
    -- This follows from `h : A ⊆ interior (closure A)`
    exact closure_mono h
  exact subset_antisymm h₁ h₂

theorem P1_stable_under_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : P1 (closure A) := by
  intro x hx
  -- First, we show `closure A ⊆ closure (interior A)`
  have h₁ : closure A ⊆ closure (interior A) := by
    have : A ⊆ closure (interior A) := hA
    have h' := closure_mono this
    simpa [closure_closure] using h'
  -- Hence, `x ∈ closure (interior A)`
  have hx₁ : x ∈ closure (interior A) := h₁ hx
  -- Next, `interior A ⊆ interior (closure A)`
  have h₂ : interior A ⊆ interior (closure A) :=
    interior_mono subset_closure
  -- Taking closures gives `closure (interior A) ⊆ closure (interior (closure A))`
  have h₃ : closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono h₂
  -- Putting everything together
  exact h₃ hx₁

theorem P2_stable_under_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P2 (interior A) := by
  intro x hx
  have hxA : x ∈ A := interior_subset hx
  have hx' : x ∈ interior (closure (interior A)) := hA hxA
  simpa [interior_interior] using hx'

theorem P3_iff_neighborhood {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A ↔ ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure A := by
  classical
  constructor
  · intro hP3
    intro x hxA
    have hxInt : x ∈ interior (closure A) := hP3 hxA
    rcases mem_interior.1 hxInt with ⟨U, hUsub, hUopen, hUx⟩
    exact ⟨U, hUopen, hUx, hUsub⟩
  · intro hNeighborhood
    intro x hxA
    rcases hNeighborhood x hxA with ⟨U, hUopen, hUx, hUsub⟩
    exact mem_interior.2 ⟨U, hUsub, hUopen, hUx⟩