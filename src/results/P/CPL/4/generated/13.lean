

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (closure A) := by
  dsimp [Topology.P1] at hA ⊢
  -- Establish the key inclusion `closure A ⊆ closure (interior (closure A))`
  have h_closure_subset :
      (closure A : Set X) ⊆ closure (interior (closure A)) := by
    -- First, `A ⊆ closure (interior (closure A))`
    have hA_subset : (A : Set X) ⊆ closure (interior (closure A)) := by
      -- From the hypothesis `A ⊆ closure (interior A)`
      have h1 : (A : Set X) ⊆ closure (interior A) := hA
      -- Monotonicity: `closure (interior A) ⊆ closure (interior (closure A))`
      have h2 : (closure (interior A) : Set X) ⊆
          closure (interior (closure A)) := by
        have h_sub : (interior A : Set X) ⊆ interior (closure A) :=
          interior_mono (subset_closure : (A : Set X) ⊆ closure A)
        exact closure_mono h_sub
      exact Set.Subset.trans h1 h2
    -- Since the right‐hand side is closed, it contains `closure A`
    exact closure_minimal hA_subset isClosed_closure
  -- Conclude the desired property
  intro x hx
  exact h_closure_subset hx