

theorem P1_mono {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → (A : Set X) ⊆ B →
      (A : Set X) ⊆ closure (interior (B : Set X)) := by
  intro hP1 hAB
  dsimp [Topology.P1] at hP1
  intro x hxA
  -- `P1` yields membership of `x` in `closure (interior A)`.
  have hx_clA : x ∈ closure (interior (A : Set X)) := hP1 hxA
  -- Monotonicity: `closure (interior A) ⊆ closure (interior B)`.
  have hSub : closure (interior (A : Set X)) ⊆
      closure (interior (B : Set X)) := by
    have hInt : interior (A : Set X) ⊆ interior (B : Set X) :=
      interior_mono hAB
    exact closure_mono hInt
  -- Conclude the desired membership.
  exact hSub hx_clA