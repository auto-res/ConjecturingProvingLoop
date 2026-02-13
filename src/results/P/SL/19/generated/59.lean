

theorem Topology.P1_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) → Topology.P1 (A := closure A) := by
  intro hP1
  dsimp [Topology.P1] at hP1 ⊢
  intro x hx_closureA
  -- `closure A ⊆ closure (interior A)`
  have hSub1 : closure A ⊆ closure (interior A) := by
    have h := closure_mono (hP1)
    simpa [closure_closure] using h
  -- `closure (interior A) ⊆ closure (interior (closure A))`
  have hSub2 : closure (interior A) ⊆ closure (interior (closure A)) := by
    have hInt : interior A ⊆ interior (closure A) :=
      Topology.interior_subset_interior_closure (A := A)
    exact closure_mono hInt
  have hx₁ : x ∈ closure (interior A) := hSub1 hx_closureA
  exact hSub2 hx₁