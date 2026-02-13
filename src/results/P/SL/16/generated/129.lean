

theorem Topology.P1_closure_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) A → Topology.P1 (X := X) (closure A) := by
  intro hP1
  dsimp [Topology.P1] at hP1 ⊢
  intro x hxClA
  -- Step 1:  `closure A ⊆ closure (interior A)` by the given `P1`.
  have h₁ : closure A ⊆ closure (interior A) :=
    Topology.closure_subset_closure_interior_of_P1 (X := X) (A := A) hP1
  -- Hence `x ∈ closure (interior A)`.
  have hxClIntA : x ∈ closure (interior A) := h₁ hxClA
  -- Step 2:  `closure (interior A) ⊆ closure (interior (closure A))`
  --          by monotonicity of `interior` and `closure`.
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) := by
    apply closure_mono
    exact Topology.interior_subset_interior_closure (X := X) (A := A)
  -- Combine the two inclusions to obtain the goal.
  exact h₂ hxClIntA