

theorem P3_interior_closure_eq_empty_iff_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) :
    interior (closure A) = (∅ : Set X) ↔ A = (∅ : Set X) := by
  classical
  constructor
  · intro hInt
    by_cases hA : (A = (∅ : Set X))
    · exact hA
    · exfalso
      -- From `A ≠ ∅` we obtain a witness `x ∈ A`.
      have hNonempty : A.Nonempty := by
        by_contra hNone
        have hEq : A = (∅ : Set X) := (Set.not_nonempty_iff_eq_empty).1 hNone
        exact hA hEq
      rcases hNonempty with ⟨x, hx⟩
      -- Thanks to `P3`, this point lies in `interior (closure A)`.
      have hxInt : x ∈ interior (closure A) := hP3 hx
      -- But `interior (closure A)` is empty, contradiction.
      have : x ∈ (∅ : Set X) := by
        simpa [hInt] using hxInt
      exact this.elim
  · intro hA
    simpa [hA, closure_empty, interior_empty]