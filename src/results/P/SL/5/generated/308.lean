

theorem closure_inter_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) ∩ interior (closure (A : Set X)) =
      interior (closure (A : Set X)) := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hxInt
    have hxCl : x ∈ closure (A : Set X) := interior_subset hxInt
    exact ⟨hxCl, hxInt⟩