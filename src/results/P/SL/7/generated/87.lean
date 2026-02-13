

theorem Topology.P1_subset_closureInteriorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A ⊆ closure (interior (closure A)) := by
  intro hP1 x hxA
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  have hIncl : closure (interior A) ⊆ closure (interior (closure A)) :=
    Topology.closureInterior_subset_closureInteriorClosure (A := A)
  exact hIncl hx_cl