

theorem Topology.frontier_closure_subset_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (closure (A : Set X)) ⊆ frontier (A : Set X) := by
  intro x hx
  rcases hx with ⟨hx_closure_cl, hx_not_int_cl⟩
  -- `x` is in `closure A`
  have hx_closure : (x : X) ∈ closure (A : Set X) := by
    simpa [closure_closure] using hx_closure_cl
  -- If `x` were in `interior A`, it would lie in `interior (closure A)`,
  -- contradicting `hx_not_int_cl`.
  have hx_not_intA : x ∉ interior (A : Set X) := by
    intro hx_intA
    have hIntMono :
        (interior (A : Set X) : Set X) ⊆ interior (closure (A : Set X)) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    have : x ∈ interior (closure (A : Set X)) := hIntMono hx_intA
    exact hx_not_int_cl this
  exact And.intro hx_closure hx_not_intA