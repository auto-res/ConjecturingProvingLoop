

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  intro x hx_closureA
  -- First, `closure A ⊆ closure (interior A)` because `closure (interior A)` is a closed
  -- set containing `A`.
  have hsubset₁ : (closure A : Set X) ⊆ closure (interior A) := by
    have hclosed : IsClosed (closure (interior A)) := isClosed_closure
    exact closure_minimal hP1 hclosed
  -- Next, `closure (interior A) ⊆ closure (interior (closure A))` by monotonicity.
  have hsubset₂ :
      (closure (interior A) : Set X) ⊆ closure (interior (closure A)) := by
    have hInt_subset : interior A ⊆ interior (closure A) := by
      exact interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono hInt_subset
  -- Chain the two inclusions to obtain the result.
  exact hsubset₂ (hsubset₁ hx_closureA)