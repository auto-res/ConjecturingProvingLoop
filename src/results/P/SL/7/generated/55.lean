

theorem Topology.interiorClosureInterior_subset_closureInteriorClosure {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆ closure (interior (closure A)) := by
  intro x hx
  have hx_cl : x ∈ closure (interior A) := interior_subset hx
  exact (Topology.closureInterior_subset_closureInteriorClosure (A := A)) hx_cl