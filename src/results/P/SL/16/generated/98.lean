

theorem Topology.interior_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure A := by
  intro x hx
  -- First, `x` lies in `closure (interior A)`.
  have hx₁ : x ∈ closure (interior A) :=
    interior_subset hx
  -- Monotonicity of `closure` turns `interior A ⊆ A` into
  -- `closure (interior A) ⊆ closure A`, so `x ∈ closure A`.
  have hx₂ : x ∈ closure A :=
    (closure_mono (interior_subset : interior A ⊆ A)) hx₁
  exact hx₂