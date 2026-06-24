

theorem P2_implies_P1_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hP2
  have hP1 : Topology.P1 A := by
    intro x hxA
    have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
    exact interior_subset hx_int
  have hP3 : Topology.P3 A := by
    intro x hxA
    have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
    have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
      apply interior_mono
      have : closure (interior A) ⊆ closure A := by
        apply closure_mono
        exact interior_subset
      exact this
    exact h_subset hx_int
  exact And.intro hP1 hP3