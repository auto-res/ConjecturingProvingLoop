

theorem P2_imp_P1_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) :
    Topology.P1 (A := A) ∧ Topology.P3 (A := A) := by
  dsimp [Topology.P2] at h
  dsimp [Topology.P1, Topology.P3]
  refine And.intro ?h1 ?h3
  · intro x hx
    have hx₁ : x ∈ interior (closure (interior A)) := h hx
    have h_subset : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    exact h_subset hx₁
  · intro x hx
    have hx₁ : x ∈ interior (closure (interior A)) := h hx
    have h_closure_subset : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    have h_interior_subset : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono h_closure_subset
    exact h_interior_subset hx₁