

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → P1 (closure A) := by
  intro hP1
  intro x hx
  -- `hP1` gives the inclusion `A ⊆ closure (interior A)`.
  have hP1_sub : (A : Set X) ⊆ closure (interior (A : Set X)) := hP1
  -- Taking closures on both sides yields
  -- `closure A ⊆ closure (interior A)`.
  have h_closure_subset :
      closure (A : Set X) ⊆ closure (interior (A : Set X)) := by
    simpa [closure_closure] using closure_mono hP1_sub
  -- Hence `x ∈ closure (interior A)`.
  have hx₁ : (x : X) ∈ closure (interior (A : Set X)) :=
    h_closure_subset hx
  -- Monotonicity of `interior`, followed by `closure`, gives
  -- `closure (interior A) ⊆ closure (interior (closure A))`.
  have h_closure_step :
      closure (interior (A : Set X)) ⊆
        closure (interior (closure (A : Set X))) := by
    have h_int_subset :
        interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono h_int_subset
  -- Combine the two inclusions to reach the goal.
  exact h_closure_step hx₁