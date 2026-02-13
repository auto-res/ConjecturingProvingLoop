

theorem Topology.closureInteriorClosure_eq_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP1 : Topology.P1 A) :
    closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  -- We prove the two inclusions separately.
  apply Set.Subset.antisymm
  ·
    exact Topology.closureInteriorClosure_subset_closure (A := A)
  ·
    -- From `P1` we have `closure A = closure (interior A)`.
    have hEq : closure (A : Set X) = closure (interior A) :=
      (Topology.P1_iff_closure_eq_closureInterior (A := A)).1 hP1
    -- `interior A ⊆ interior (closure A)` by monotonicity of `interior`.
    have hIncl : closure (interior A) ⊆
        closure (interior (closure (A : Set X))) := by
      apply closure_mono
      exact Topology.interior_subset_interiorClosure (A := A)
    -- Rewrite using the equality obtained from `P1`.
    simpa [hEq] using hIncl