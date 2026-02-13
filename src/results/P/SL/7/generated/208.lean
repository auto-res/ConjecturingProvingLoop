

theorem Topology.P1_subset_closureInteriorClosureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A ⊆ closure (interior (closure (interior A))) := by
  intro hP1 x hxA
  -- From `P1` we get membership in `closure (interior A)`.
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- Use the established inclusion
  -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`.
  have hIncl :
      closure (interior A) ⊆ closure (interior (closure (interior A))) :=
    Topology.closureInterior_subset_closureInteriorClosureInterior (A := A)
  exact hIncl hx_cl