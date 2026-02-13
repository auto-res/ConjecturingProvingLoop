

theorem Topology.P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) A → Topology.P1 (X := X) (closure (A : Set X)) := by
  intro hP3
  dsimp [Topology.P1] -- unfold the definition of P1
  intro x hx_clA
  -- We first show that `closure A ⊆ closure (interior (closure A))`
  have h_subset : (closure (A : Set X)) ⊆ closure (interior (closure A)) := by
    -- Step 1: `A ⊆ closure (interior (closure A))`
    have hA_subset : (A : Set X) ⊆ closure (interior (closure A)) := by
      intro y hyA
      have hy_int : y ∈ interior (closure A) := hP3 hyA
      exact subset_closure hy_int
    -- Step 2: take closures on both sides of the previous inclusion
    have h_closure_subset :
        closure (A : Set X) ⊆ closure (closure (interior (closure A))) :=
      closure_mono hA_subset
    simpa [closure_closure] using h_closure_subset
  exact h_subset hx_clA