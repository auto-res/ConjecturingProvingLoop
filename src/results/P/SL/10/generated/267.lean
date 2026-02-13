

theorem Topology.closure_interior_diff_interior_closure_subset_boundary
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) \ interior (closure A) ⊆ closure A \ interior A := by
  intro x hx
  rcases hx with ⟨hxClIntA, hxNotIntClA⟩
  -- `x` lies in `closure A` because `interior A ⊆ A`.
  have hxClA : x ∈ closure A :=
    (Topology.closure_interior_subset_closure (X := X) (A := A)) hxClIntA
  -- Show that `x ∉ interior A`, otherwise we contradict `hxNotIntClA`.
  have hxNotIntA : x ∉ interior A := by
    intro hxIntA
    -- `interior A ⊆ interior (closure A)`, so `x` would be in the latter.
    have hxIntClA : x ∈ interior (closure A) :=
      (Topology.interior_subset_interior_closure (X := X) (A := A)) hxIntA
    exact hxNotIntClA hxIntClA
  exact And.intro hxClA hxNotIntA