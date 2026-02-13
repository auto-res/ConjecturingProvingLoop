

theorem interior_closure_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (A : Set X).Nonempty →
      (interior (closure (A : Set X))).Nonempty := by
  intro hP1 hA
  -- Obtain a point in the interior of `A` using the existing lemma.
  rcases (Topology.interior_nonempty_of_P1 (X := X) (A := A) hP1 hA) with ⟨x, hxIntA⟩
  -- Monotonicity of `interior` yields the desired inclusion.
  have hMono : interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure (A : Set X))
  exact ⟨x, hMono hxIntA⟩