

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  unfold Topology.P2 Topology.P3 at *
  intro x hxA
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  have hint : closure (interior A) ⊆ closure A := closure_mono interior_subset
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono hint
  exact hsubset hx_int