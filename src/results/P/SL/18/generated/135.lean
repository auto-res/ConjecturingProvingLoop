

theorem dense_inter_open_nonempty
    {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hDense : Dense (A : Set X)) (hU_open : IsOpen U)
    (hU_nonempty : (U : Set X).Nonempty) :
    (A ∩ U : Set X).Nonempty := by
  classical
  -- Choose a point `x` in the nonempty open set `U`.
  rcases hU_nonempty with ⟨x, hxU⟩
  -- Density provides that `x` lies in the closure of `A`.
  have hx_closure : x ∈ closure (A : Set X) := hDense x
  -- The characterization of the closure via open neighbourhoods
  -- yields a point of `A` inside `U`.
  have hIntersect : (U ∩ A : Set X).Nonempty :=
    (mem_closure_iff).1 hx_closure U hU_open hxU
  -- Reorder the intersection to match the goal.
  simpa [Set.inter_comm] using hIntersect