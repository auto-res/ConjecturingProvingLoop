

theorem Topology.P2_iff_subset_and_closure_subset {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (A := A) ↔
      (A ⊆ interior (closure A) ∧ closure A ⊆ closure (interior A)) := by
  constructor
  · intro hP2
    -- The inclusion `A ⊆ interior (closure A)` follows from `P2 → P3`.
    have hP3 : Topology.P3 (A := A) := Topology.P2_implies_P3 (A := A) hP2
    -- From `P2 → P1` we obtain the equality of the two closures.
    have hP1 : Topology.P1 (A := A) := Topology.P2_implies_P1 (A := A) hP2
    have hEq : closure A = closure (interior A) :=
      Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
    -- Rewrite `subset_rfl` using this equality to get the desired inclusion.
    have hClosIncl : closure A ⊆ closure (interior A) := by
      simpa [hEq] using (subset_rfl : closure A ⊆ closure A)
    exact And.intro hP3 hClosIncl
  · rintro ⟨hSubA, hClosIncl⟩
    -- To establish `P2`, start from `A ⊆ interior (closure A)`.
    dsimp [Topology.P2]
    intro x hxA
    have hxInt : x ∈ interior (closure A) := hSubA hxA
    -- Use monotonicity of `interior` with the inclusion of the closures.
    have hIntMono :
        interior (closure A) ⊆ interior (closure (interior A)) :=
      interior_mono hClosIncl
    exact hIntMono hxInt