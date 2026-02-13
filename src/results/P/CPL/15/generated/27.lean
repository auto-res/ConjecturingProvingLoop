

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) : P1 (closure A) := by
  intro x hx
  -- Step 1 : move from `x ∈ closure A` to `x ∈ closure (interior A)`.
  have hx₁ : (x : X) ∈ closure (interior A) := by
    -- `closure A ⊆ closure (closure (interior A))` thanks to `h`.
    have h₁ : (x : X) ∈ closure (closure (interior A)) :=
      (closure_mono h) hx
    -- Remove the superfluous `closure`.
    simpa [closure_closure] using h₁
  -- Step 2 : `closure (interior A) ⊆ closure (interior (closure A))`.
  have h_subset :
      (closure (interior A) : Set X) ⊆ closure (interior (closure A)) := by
    have h_inner : (interior A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono h_inner
  -- Finish.
  exact h_subset hx₁