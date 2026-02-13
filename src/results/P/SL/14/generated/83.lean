

theorem Topology.closureInterior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- Show `x` lies in `closure (interior A)`
  have hxA : (x : X) ∈ closure (interior A) := by
    -- `interior (A ∩ B)` is contained in `interior A`
    have h_intA : (interior (A ∩ B) : Set X) ⊆ interior A := by
      exact interior_mono (by
        intro y hy
        exact hy.1)
    exact (closure_mono h_intA) hx
  -- Show `x` lies in `closure (interior B)`
  have hxB : (x : X) ∈ closure (interior B) := by
    -- `interior (A ∩ B)` is contained in `interior B`
    have h_intB : (interior (A ∩ B) : Set X) ⊆ interior B := by
      exact interior_mono (by
        intro y hy
        exact hy.2)
    exact (closure_mono h_intB) hx
  exact And.intro hxA hxB