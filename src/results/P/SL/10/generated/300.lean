

theorem Topology.nonempty_of_nonempty_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (interior (closure A)).Nonempty → A.Nonempty := by
  intro hInt
  rcases hInt with ⟨x, hxInt⟩
  -- `x` lies in the closure of `A`.
  have hxCl : (x : X) ∈ closure A := interior_subset hxInt
  -- If `A` were empty, its closure would also be empty, contradicting `hxCl`.
  by_cases hA : A.Nonempty
  · exact hA
  ·
    have hAempty : (A : Set X) = ∅ :=
      (Set.not_nonempty_iff_eq_empty).1 hA
    have : (x : X) ∈ (∅ : Set X) := by
      simpa [hAempty, closure_empty] using hxCl
    cases this