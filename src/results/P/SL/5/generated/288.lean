

theorem closure_inter_interior_eq_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure ((A : Set X) ∩ interior A) = closure (interior A) := by
  have h : ((A : Set X) ∩ interior A) = interior A := by
    ext x
    constructor
    · intro hx; exact hx.2
    · intro hx; exact ⟨interior_subset hx, hx⟩
  simpa [h]