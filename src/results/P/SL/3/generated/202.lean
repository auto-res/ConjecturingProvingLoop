

theorem closureInterior_diff_interior_subset_boundary {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (A : Set X)) \ interior (A : Set X) ⊆
      closure (A : Set X) \ interior (A : Set X) := by
  intro x hx
  rcases hx with ⟨hx_clInt, hx_notInt⟩
  have hx_clA : (x : X) ∈ closure (A : Set X) :=
    (closure_interior_subset_closure (A := A)) hx_clInt
  exact And.intro hx_clA hx_notInt