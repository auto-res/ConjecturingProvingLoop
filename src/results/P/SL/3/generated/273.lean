

theorem interior_closure_diff_interior_subset_boundary {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (A : Set X)) \ interior (A : Set X) ⊆
      closure (A : Set X) \ interior (A : Set X) := by
  intro x hx
  rcases hx with ⟨hxIntCl, hxNotInt⟩
  have hxCl : (x : X) ∈ closure (A : Set X) :=
    interior_subset (s := closure (A : Set X)) hxIntCl
  exact And.intro hxCl hxNotInt