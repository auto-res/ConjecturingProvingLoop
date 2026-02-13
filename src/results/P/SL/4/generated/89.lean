

theorem P1_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  dsimp [Topology.P1] at hP1
  dsimp [Topology.P1]
  intro x hx
  -- First, upgrade `x ∈ closure A` to `x ∈ closure (interior A)`.
  have h₁ : closure A ⊆ closure (interior A) := by
    have h := closure_mono hP1
    simpa [closure_closure] using h
  have hx₁ : x ∈ closure (interior A) := h₁ hx
  -- Next, use monotonicity to land in `closure (interior (closure A))`.
  have h₂ :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_interior_subset_closure_interior_closure (X := X) (A := A)
  exact h₂ hx₁