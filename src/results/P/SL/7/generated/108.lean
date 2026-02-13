

theorem IsOpen_P2' {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P2 A := by
  -- Unfold the definition of `P2`.
  dsimp [Topology.P2]
  -- Prove the inclusion pointwise.
  intro x hxA
  -- Since `A` is open, we can place `x` inside `interior (closure A)`.
  have hx_in_int_closureA : x ∈ interior (closure A) := by
    have hIncl : (A : Set X) ⊆ interior (closure A) :=
      interior_maximal subset_closure hA
    exact hIncl hxA
  -- Relate `interior (closure (interior A))` to `interior (closure A)`
  -- using the fact that `interior A = A`.
  have hEq : interior (closure (interior A)) = interior (closure A) := by
    simpa [hA.interior_eq]
  -- Rewrite and finish.
  simpa [hEq] using hx_in_int_closureA