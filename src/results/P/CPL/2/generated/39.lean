

theorem P2_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P2 (X:=X) A) : Topology.P2 (X:=X×Y) (A ×ˢ (Set.univ : Set Y)) := by
  -- `univ` satisfies `P2`, so we can apply the general `P2_prod` theorem
  have hB : Topology.P2 (X := Y) (Set.univ : Set Y) := by
    simpa using (P2_univ (X := Y))
  simpa using (P2_prod (A := A) (B := (Set.univ : Set Y)) hA hB)

theorem P1_iterate {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (X:=X) (closure (interior (closure (interior A)))) := by
  -- Unfold the definition of `P1`
  unfold Topology.P1
  intro x hx
  -- Let `S := interior (closure (interior A))`; we will show
  -- `closure S ⊆ closure (interior (closure S))`
  have h_subset :
      (closure (interior (closure (interior A))) : Set X) ⊆
        closure (interior (closure (interior (closure (interior A))))) := by
    -- First, prove `interior S ⊆ interior (closure S)`
    have h_int :
        (interior (closure (interior A)) : Set X) ⊆
          interior (closure (interior (closure (interior A)))) := by
      -- `interior (closure (interior A))` is open and contained in its closure
      simpa using
        (interior_maximal
            (subset_closure :
              (interior (closure (interior A)) : Set X) ⊆
                closure (interior (closure (interior A))))
            (isOpen_interior :
              IsOpen (interior (closure (interior A)))))
    -- Taking closures yields the desired inclusion
    exact closure_mono h_int
  -- Finish by applying the inclusion to the given point
  exact h_subset hx

theorem exists_finite_P1 {X : Type*} [TopologicalSpace X] [Finite X] : ∃ A : Set X, Topology.P1 (X:=X) A := by
  refine ⟨(Set.univ : Set X), ?_⟩
  simpa using (Topology.P1_univ (X := X))