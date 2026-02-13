

theorem Topology.P1_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) A → Topology.P1 (X := X) (closure (A : Set X)) := by
  intro hP1
  dsimp [Topology.P1] at hP1 ⊢
  intro x hx_closureA
  -- Step 1: from `hP1`, lift the inclusion to closures.
  have h_cl1 : closure (A : Set X) ⊆ closure (closure (interior A)) :=
    closure_mono hP1
  have hx₁ : x ∈ closure (closure (interior A)) := h_cl1 hx_closureA
  -- Simplify the double closure.
  have hx₂ : x ∈ closure (interior A) := by
    simpa [closure_closure] using hx₁
  -- Step 2: relate `closure (interior A)` to `closure (interior (closure A))`.
  have h_cl2 : closure (interior A) ⊆ closure (interior (closure A)) := by
    have h_int : interior A ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono h_int
  exact h_cl2 hx₂