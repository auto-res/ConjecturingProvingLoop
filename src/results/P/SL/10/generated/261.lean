

theorem Topology.nonempty_iff_nonempty_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    A.Nonempty ↔ (closure A).Nonempty := by
  classical
  constructor
  · intro hA
    exact hA.closure
  · intro hCl
    by_contra hA
    -- From `¬ A.Nonempty` obtain `A = ∅`.
    have hAempty : A = (∅ : Set X) :=
      (Set.not_nonempty_iff_eq_empty).1 hA
    -- Hence `closure A = ∅` by the existing characterization.
    have hClEmpty : closure A = (∅ : Set X) :=
      ((Topology.closure_eq_empty_iff (X := X) (A := A)).2 hAempty)
    -- But this contradicts the assumed non‐emptiness of `closure A`.
    rcases hCl with ⟨x, hx⟩
    have : x ∈ (∅ : Set X) := by
      simpa [hClEmpty] using hx
    cases this