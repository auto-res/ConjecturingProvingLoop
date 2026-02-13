

theorem Topology.P3_of_interior_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) = (Set.univ : Set X) → Topology.P3 A := by
  intro hIntEq
  intro x hxA
  -- `x` lies in `interior A` because `interior A = univ`.
  have hxIntA : x ∈ interior (A : Set X) := by
    have : x ∈ (Set.univ : Set X) := by
      simp
    simpa [hIntEq] using this
  -- Monotonicity of `interior` for the inclusion `A ⊆ closure A`.
  have hSubset :
      (interior (A : Set X) : Set X) ⊆ interior (closure (A : Set X)) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact hSubset hxIntA