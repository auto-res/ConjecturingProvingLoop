

theorem P1_of_subset_between {X : Type*} [TopologicalSpace X] {A B : Set X} :
    (A : Set X) ⊆ B →
    B ⊆ closure (interior (A : Set X)) →
    Topology.P1 B := by
  intro hAB hBcl
  dsimp [Topology.P1] at *
  intro x hxB
  -- First, use the hypothesis `hBcl` to place `x` inside `closure (interior A)`.
  have hx_clA : x ∈ closure (interior (A : Set X)) := hBcl hxB
  -- Monotonicity: `interior A ⊆ interior B` because `A ⊆ B`.
  have hInt : interior (A : Set X) ⊆ interior (B : Set X) :=
    interior_mono hAB
  -- Taking closures preserves inclusions.
  have hCl : closure (interior (A : Set X)) ⊆
      closure (interior (B : Set X)) := closure_mono hInt
  -- Combine the facts to land in the desired target set.
  exact hCl hx_clA