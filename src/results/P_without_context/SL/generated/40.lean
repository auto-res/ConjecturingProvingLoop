

theorem P2_implies_P1_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := A) ∧ Topology.P3 (A := A) := by
  intro h
  -- Prove P1 : A ⊆ closure (interior A)
  have h1 : A ⊆ closure (interior A) := by
    intro x hx
    have : x ∈ interior (closure (interior A)) := h hx
    exact interior_subset this
  -- Prove P3 : A ⊆ interior (closure A)
  have h2 : A ⊆ interior (closure A) := by
    intro x hx
    have hx' : x ∈ interior (closure (interior A)) := h hx
    have inc : interior (closure (interior A)) ⊆ interior (closure A) := by
      have hsub : closure (interior A) ⊆ closure A := by
        exact closure_mono interior_subset
      exact interior_mono hsub
    exact inc hx'
  exact And.intro h1 h2