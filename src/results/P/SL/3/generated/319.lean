

theorem nonempty_iff_interior_closure_nonempty_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (A : Set X)) :
    (A : Set X).Nonempty ↔ (interior (closure (A : Set X))).Nonempty := by
  classical
  constructor
  · intro hA
    exact
      interior_closure_nonempty_of_P3 (A := A) hA hP3
  · intro hIntCl
    by_cases hA : (A : Set X).Nonempty
    · exact hA
    · -- Derive a contradiction from `hIntCl` and `hA = ∅`.
      have hA_eq : (A : Set X) = (∅ : Set X) :=
        Set.not_nonempty_iff_eq_empty.mp hA
      have hIntEmpty :
          interior (closure (A : Set X)) = (∅ : Set X) := by
        simpa [hA_eq, closure_empty, interior_empty]
      rcases hIntCl with ⟨x, hx⟩
      have : (x : X) ∈ (∅ : Set X) := by
        simpa [hIntEmpty] using hx
      cases this