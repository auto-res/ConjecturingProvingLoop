

theorem boundary_interior_subset_boundary {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (A : Set X)) \ interior (A : Set X) ⊆
      closure (A : Set X) \ interior (A : Set X) := by
  intro x hx
  rcases hx with ⟨hxClInt, hxNotIntA⟩
  have hxClA : (x : X) ∈ closure (A : Set X) :=
    (closure_interior_subset_closure (A := A)) hxClInt
  exact And.intro hxClA hxNotIntA