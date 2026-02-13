

theorem interior_subset_inter_self_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ⊆ A ∩ interior (closure A) := by
  intro x hxIntA
  -- `x` lies in `A` because it lies in `interior A`.
  have hxA : x ∈ A := interior_subset hxIntA
  -- `x` also lies in `interior (closure A)` by monotonicity of `interior`.
  have hxIntClA : x ∈ interior (closure A) :=
    Topology.interior_subset_interior_closure (A := A) hxIntA
  exact And.intro hxA hxIntClA