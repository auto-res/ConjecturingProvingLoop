

theorem interior_inter_interior_closure_eq_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∩ interior (closure A) = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hxIntA
    have hxIntCl : x ∈ interior (closure (A : Set X)) :=
      (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hxIntA
    exact ⟨hxIntA, hxIntCl⟩