

theorem boundary_closure_subset_boundary {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) \ interior (closure (A : Set X)) ⊆
      closure (A : Set X) \ interior (A : Set X) := by
  intro x hx
  rcases hx with ⟨hxCl, hxNotIntCl⟩
  -- If `x` were in `interior A`, then it would also lie in `interior (closure A)`,
  -- contradicting `hxNotIntCl`.
  have hxNotIntA : (x : X) ∉ interior (A : Set X) := by
    intro hxIntA
    have : (x : X) ∈ interior (closure (A : Set X)) := by
      have h_subset :
          interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
        interior_mono (subset_closure : (A : Set X) ⊆ closure A)
      exact h_subset hxIntA
    exact hxNotIntCl this
  exact And.intro hxCl hxNotIntA