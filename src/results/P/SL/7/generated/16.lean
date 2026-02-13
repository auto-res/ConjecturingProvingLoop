

theorem Topology.interior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hA : A.Nonempty) : (interior A).Nonempty := by
  classical
  by_contra hIntEmpty
  have hIntEq : interior A = (∅ : Set X) := by
    simpa [Set.not_nonempty_iff_eq_empty] using hIntEmpty
  have hClosureEq : closure (interior A) = (∅ : Set X) := by
    simpa [hIntEq] using
      (closure_empty : closure (∅ : Set X) = (∅ : Set X))
  rcases hA with ⟨x, hx⟩
  have hx_cl : x ∈ closure (interior A) := hP1 hx
  have : x ∈ (∅ : Set X) := by
    simpa [hClosureEq] using hx_cl
  cases this