

theorem P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro h
  dsimp [P2] at h
  dsimp [P1]
  intro x hx
  exact
    (interior_subset :
      interior (closure (interior A)) ⊆ closure (interior A)) (h hx)

theorem P2_open_set {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P2 A := by
  intro hA
  dsimp [P2]
  intro x hx
  -- First, view `hx` as a membership in `interior A`
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  -- `interior A` is an open subset of `closure (interior A)`
  have h_subset : interior A ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  exact h_subset hx_int

theorem P1_iff_closure_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  dsimp [P1]
  constructor
  · intro hP1
    -- `closure (interior A)` is always contained in `closure A`
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    -- From `hP1 : A ⊆ closure (interior A)` we deduce the reverse inclusion
    have h₂ : closure A ⊆ closure (interior A) := by
      have : closure A ⊆ closure (closure (interior A)) :=
        closure_mono hP1
      simpa [closure_closure] using this
    exact le_antisymm h₁ h₂
  · intro hEq
    intro x hxA
    have hx_closureA : x ∈ closure A := subset_closure hxA
    simpa [hEq.symm] using hx_closureA

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hA hB
  dsimp [P1] at *
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hx_closureA : x ∈ closure (interior A) := hA hxA
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior A ⊆ interior (A ∪ B) :=
          interior_mono (by
            intro y hy
            exact Or.inl hy)
        exact this
      exact hsubset hx_closureA
  | inr hxB =>
      -- `x ∈ B`
      have hx_closureB : x ∈ closure (interior B) := hB hxB
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior B ⊆ interior (A ∪ B) :=
          interior_mono (by
            intro y hy
            exact Or.inr hy)
        exact this
      exact hsubset hx_closureB