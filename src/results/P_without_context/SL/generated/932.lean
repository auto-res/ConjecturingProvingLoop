

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 A := by
  intro hP2
  intro x hxA
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  have hx_cl : x ∈ closure (interior A) := interior_subset hx_int
  exact hx_cl