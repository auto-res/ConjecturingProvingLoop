

theorem interior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : (A : Set X).Nonempty) (hP1 : Topology.P1 (A : Set X)) :
    (interior (A : Set X)).Nonempty := by
  classical
  rcases hA with ⟨x, hxA⟩
  have hx_cl : (x : X) ∈ closure (interior (A : Set X)) := hP1 hxA
  by_cases hInt : (interior (A : Set X)).Nonempty
  · exact hInt
  · -- If `interior A` were empty, `x` would lie in `closure ∅ = ∅`, contradiction.
    have hInt_eq_empty : interior (A : Set X) = (∅ : Set X) :=
      Set.not_nonempty_iff_eq_empty.mp hInt
    have : (x : X) ∈ (∅ : Set X) := by
      simpa [hInt_eq_empty, closure_empty] using hx_cl
    cases this