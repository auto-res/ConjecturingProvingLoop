

theorem Topology.P2_imp_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  dsimp [Topology.P2, Topology.P3]
  intro hP2 x hxA
  have hx1 : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_closure : closure (interior A) ⊆ closure A := by
    simpa using closure_mono (interior_subset : interior A ⊆ A)
  have h_incl : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_closure
  exact h_incl hx1