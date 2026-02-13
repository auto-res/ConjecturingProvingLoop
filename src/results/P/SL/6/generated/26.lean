

theorem P1_closure_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → Topology.P1 (closure (A : Set X)) := by
  intro hA
  dsimp [Topology.P1] at hA ⊢
  -- First, lift the inclusion to the closures
  have h₁ : closure (A : Set X) ⊆ closure (interior A) := by
    simpa [closure_closure] using (closure_mono hA)
  -- Next, use monotonicity of interior and closure
  have h₂ : closure (interior A) ⊆ closure (interior (closure (A : Set X))) := by
    have h : interior A ⊆ interior (closure (A : Set X)) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono h
  exact h₁.trans h₂