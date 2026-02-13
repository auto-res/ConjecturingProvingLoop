

theorem interior_closure_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hne : A.Nonempty) :
    (interior (closure A)).Nonempty := by
  -- First, obtain a point in `interior A` using an existing lemma.
  have hIntA : (interior A).Nonempty :=
    Topology.interior_nonempty_of_P1 (A := A) hP1 hne
  rcases hIntA with ⟨x, hxIntA⟩
  -- Monotonicity of `interior` guarantees the required membership.
  have hxIntCl : x ∈ interior (closure A) := by
    have hsubset : interior A ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact hsubset hxIntA
  exact ⟨x, hxIntCl⟩