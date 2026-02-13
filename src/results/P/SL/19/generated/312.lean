

theorem Topology.frontier_closure_interior_subset_frontier {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    frontier (closure (interior A)) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxClos, hxNotInt⟩
  -- `hxClos` lives in `closure (closure (interior A))`, simplify the double closure
  have hxClosInt : x ∈ closure (interior A) := by
    simpa [closure_closure] using hxClos
  -- From the monotonicity of `closure`, obtain `x ∈ closure A`
  have hxClosA : x ∈ closure A := by
    have hSub : closure (interior A) ⊆ closure A :=
      Topology.closure_interior_subset_closure (A := A)
    exact hSub hxClosInt
  -- Show that `x ∉ interior A`; otherwise we contradict `hxNotInt`
  have hxNotIntA : x ∉ interior A := by
    intro hxIntA
    have hSubInt :
        interior A ⊆ interior (closure (interior A)) :=
      Topology.interior_subset_interior_closure_interior (A := A)
    have : x ∈ interior (closure (interior A)) := hSubInt hxIntA
    exact hxNotInt this
  -- Assemble the two facts to conclude `x ∈ frontier A`
  exact And.intro hxClosA hxNotIntA