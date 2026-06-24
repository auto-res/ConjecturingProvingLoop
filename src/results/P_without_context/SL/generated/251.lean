

theorem Topology.P2_implies_P1_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hP2
  have hP1 : Topology.P1 A := by
    intro x hx
    have hx_int : x ∈ interior (closure (interior A)) := hP2 hx
    exact interior_subset hx_int
  have hP3 : Topology.P3 A := by
    intro x hx
    have hx_int : x ∈ interior (closure (interior A)) := hP2 hx
    have h_closure_subset : closure (interior A) ⊆ closure A := by
      have h_int_subset : interior A ⊆ A := interior_subset
      exact closure_mono h_int_subset
    have h_int_subset : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono h_closure_subset
    exact h_int_subset hx_int
  exact And.intro hP1 hP3