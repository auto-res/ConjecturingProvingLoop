

theorem Topology.P2_implies_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  intro x hxA
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  have hx_clo : x ∈ closure (interior A) := interior_subset hx_int
  exact hx_clo