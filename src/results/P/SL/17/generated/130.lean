

theorem Topology.interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior (closure A)) := by
  intro x hx
  -- Step 1: `x ∈ interior (closure A)` by monotonicity of `interior`
  have hxIntClosure : x ∈ interior (closure A) := by
    have h_mono : interior A ⊆ interior (closure A) :=
      interior_mono (subset_closure : A ⊆ closure A)
    exact h_mono hx
  -- Step 2: `interior (closure A)` is contained in its closure
  exact (subset_closure : interior (closure A) ⊆
      closure (interior (closure A))) hxIntClosure