

theorem P2_implies_P1_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : P2 (X := X) A) :
    P1 (X := X) (closure (A : Set X)) := by
  dsimp [P1] at *
  intro x hx
  -- Step 1: `closure A ⊆ closure (interior A)` via `P2`.
  have h₁ : closure (A : Set X) ⊆ closure (interior A) :=
    P2_closure_subset (X := X) (A := A) hA
  -- Step 2: `closure (interior A) ⊆ closure (interior (closure A))`.
  have h₂ : closure (interior A) ⊆ closure (interior (closure (A : Set X))) :=
    closure_interior_subset_closure_interior_closure (X := X) A
  -- Combine the two inclusions.
  have hx' : x ∈ closure (interior A) := h₁ hx
  exact h₂ hx'