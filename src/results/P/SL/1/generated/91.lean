

theorem Topology.interior_closure_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) :
    interior (closure A) = (Set.univ : Set X) := by
  -- Since `interior A` is dense, its closure is the whole space.
  have h_closure : closure (interior A) = (Set.univ : Set X) := by
    simpa using h.closure_eq
  -- Monotonicity of `interior` and `closure` gives a useful inclusion.
  have h_mono : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    have : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    exact this
  -- Establish the desired equality by two inclusions.
  apply Set.Subset.antisymm
  · -- Trivial inclusion.
    intro x _
    simp
  · -- Use the density information to obtain the reverse inclusion.
    intro x hx
    have hx' : x ∈ interior (closure (interior A)) := by
      simpa [h_closure, interior_univ] using hx
    exact h_mono hx'