

theorem Topology.P1_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A := A)) : Topology.P1 (A := closure A) := by
  dsimp [Topology.P1] at hP1 ⊢
  intro x hx_closureA
  -- First, use `hP1` to see that `closure A ⊆ closure (interior A)`.
  have h₁ : closure A ⊆ closure (interior A) := by
    have hA : (A : Set X) ⊆ closure (interior A) := hP1
    have : closure A ⊆ closure (closure (interior A)) := closure_mono hA
    simpa [closure_closure] using this
  -- Next, note that `closure (interior A) ⊆ closure (interior (closure A))`.
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) := by
    have : interior A ⊆ interior (closure A) := interior_mono subset_closure
    exact closure_mono this
  -- Chain the inclusions to reach the desired membership.
  exact h₂ (h₁ hx_closureA)