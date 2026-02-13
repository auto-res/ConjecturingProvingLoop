

theorem closure_interior_eq_closure_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → closure (interior (A : Set X)) = closure A := by
  intro hP1
  apply Set.Subset.antisymm
  · exact closure_mono (interior_subset : (interior (A : Set X)) ⊆ A)
  · exact closure_minimal hP1 (isClosed_closure)

theorem P3_iff_P2_of_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (A : Set X) = closure (interior A)) : P3 A ↔ P2 A := by
  have hint :
      interior (closure (A : Set X)) =
        interior (closure (interior (A : Set X))) := by
    simpa [h]
  constructor
  · intro hP3
    intro x hx
    have hx' : x ∈ interior (closure (A : Set X)) := hP3 hx
    simpa [hint] using hx'
  · intro hP2
    exact P3_of_P2 hP2