

theorem Topology.P3_implies_subset_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A →
      (A : Set X) ⊆
        interior (closure (interior (closure (A : Set X)))) := by
  intro hP3 x hxA
  -- Step 1: from `P3` obtain that `x` is in `interior (closure A)`.
  have hx_int_cl : x ∈ interior (closure (A : Set X)) := hP3 hxA
  -- Step 2: establish the inclusion
  --   `interior (closure A) ⊆ interior (closure (interior (closure A)))`.
  have hIncl :
      (interior (closure (A : Set X)) : Set X) ⊆
        interior (closure (interior (closure (A : Set X)))) := by
    -- `P3` gives `closure A ⊆ closure (interior (closure A))`.
    have hClSub :
        (closure (A : Set X)) ⊆
          closure (interior (closure (A : Set X))) :=
      Topology.P3_implies_closure_subset_closure_interior_closure
        (A := A) hP3
    -- Apply monotonicity of `interior` to the inclusion of closures.
    exact interior_mono hClSub
  -- Step 3: combine the facts to obtain the desired membership.
  exact hIncl hx_int_cl