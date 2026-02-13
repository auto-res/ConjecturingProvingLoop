

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior A) := by
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  intro x hx
  -- First, show the needed set inclusion.
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    -- `interior (interior A)` is contained in `interior (closure (interior A))`.
    have h : interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono (subset_closure : (interior A : Set X) ⊆ closure (interior A))
    simpa [interior_interior] using h
  -- Apply the inclusion to the given point.
  have : x ∈ interior (closure (interior A)) := hsubset hx
  -- Rewrite the goal and finish.
  simpa [interior_interior] using this

theorem P1_iff_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  -- Unfold the definition of `P1`.
  unfold P1
  constructor
  · intro hA
    -- `closure (interior A)` is contained in `closure A`.
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    -- Taking closures of the hypothesis gives the reverse inclusion.
    have h₂ : closure A ⊆ closure (interior A) := by
      have : closure A ⊆ closure (closure (interior A)) := closure_mono hA
      simpa [closure_closure] using this
    exact subset_antisymm h₁ h₂
  · intro h_eq
    intro x hx
    -- Every point of `A` lies in `closure A`, which equals `closure (interior A)`.
    have : x ∈ closure A := subset_closure hx
    simpa [h_eq] using this

theorem P2_iff_P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A ↔ P1 A := by
  constructor
  · intro h
    exact P1_of_P2 h
  · intro _
    exact P2_of_open hA