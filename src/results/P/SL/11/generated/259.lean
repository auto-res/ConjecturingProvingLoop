

theorem interior_closure_iInter_eq {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, IsClosed (A i)) :
    interior (closure (⋂ i, A i)) = interior (⋂ i, A i) := by
  have hEq : closure (⋂ i, A i) = (⋂ i, A i) :=
    (closure_iInter_eq_iInter (A := A) (hA := hA))
  simpa [hEq]