

theorem Topology.P2_closure_implies_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure A) → Topology.P3 (X := X) A := by
  intro hP2 x hxA
  -- First, regard `x` as a point of `closure A`.
  have hxCl : x ∈ closure A := subset_closure hxA
  -- Apply `P2` for `closure A`, landing `x` in `interior (closure (interior (closure A)))`.
  have hxInt₁ : x ∈ interior (closure (interior (closure A))) := hP2 hxCl
  -- Use the equality
  --   `interior (closure (interior (closure A))) = interior (closure A)`
  -- to rewrite the membership.
  have hxInt₂ : x ∈ interior (closure A) := by
    simpa [Topology.interior_closure_interior_closure_eq_interior_closure
      (X := X) (A := A)] using hxInt₁
  -- Conclude the desired statement of `P3`.
  exact hxInt₂