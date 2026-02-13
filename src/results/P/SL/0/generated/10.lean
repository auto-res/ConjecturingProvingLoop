

theorem P1_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  dsimp [Topology.P1] at hP1 ⊢
  -- First, `closure A ⊆ closure (interior A)` by monotonicity of `closure`.
  have h₁ : closure A ⊆ closure (interior A) := by
    have : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
    simpa using this
  -- Next, `closure (interior A) ⊆ closure (interior (closure A))` as
  -- `interior A ⊆ interior (closure A)`.
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) := by
    apply closure_mono
    exact interior_mono subset_closure
  -- Putting the two inclusions together yields the desired result.
  exact h₁.trans h₂