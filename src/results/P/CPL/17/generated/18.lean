

theorem P2_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Topology.P2 A → A = interior A := by
  intro hA_closed hP2A
  apply Set.Subset.antisymm
  · intro x hxA
    have hx_mem : x ∈ interior (closure (interior A)) := hP2A hxA
    have h_subset : interior (closure (interior A)) ⊆ interior A := by
      -- First, establish `closure (interior A) ⊆ A`.
      have h_closure_subset : closure (interior A) ⊆ A := by
        have h_int_subset : (interior A : Set X) ⊆ A := interior_subset
        have h_closure_subset' : closure (interior A) ⊆ closure A :=
          closure_mono h_int_subset
        simpa [hA_closed.closure_eq] using h_closure_subset'
      -- Use monotonicity of interior to get the desired inclusion.
      exact interior_mono h_closure_subset
    exact h_subset hx_mem
  · exact interior_subset

theorem P1_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : Topology.P1 A → Topology.P1 (A ×ˢ (Set.univ : Set Y)) := by
  intro hP1A
  have hP1_univ : Topology.P1 (Set.univ : Set Y) := P1_univ (X := Y)
  simpa using (P1_prod (A := A) (B := (Set.univ : Set Y)) hP1A hP1_univ)