

theorem closure_inter_interior_eq_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (A : Set X)) ∩ interior A = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hxInt
    have hxCl : x ∈ closure (interior (A : Set X)) := subset_closure hxInt
    exact ⟨hxCl, hxInt⟩