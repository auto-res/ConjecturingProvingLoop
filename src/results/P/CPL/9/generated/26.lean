

theorem P1_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 (A := A)) : closure A ⊆ closure (interior A) := by
  intro x hx
  have h' : x ∈ closure (closure (interior A)) := (closure_mono hA) hx
  simpa [closure_closure] using h'

theorem P3_of_dense_subset {X : Type*} [TopologicalSpace X] {A B : Set X} (h_sub : A ⊆ B) (h_dense : Dense A) : Topology.P3 (A := B) := by
  intro x hxB
  -- Step 1: the closure of `A` is the whole space.
  have h_closureA_univ : (closure (A) : Set X) = (Set.univ : Set X) := by
    simpa using h_dense.closure_eq
  -- Step 2: deduce that the closure of `B` is also the whole space.
  have h_closureB_univ : (closure (B) : Set X) = (Set.univ : Set X) := by
    -- We already know `closure A ⊆ closure B`.
    have h_subset : (closure A : Set X) ⊆ closure B := closure_mono h_sub
    -- Hence `univ ⊆ closure B`.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure B := by
      intro y hy
      have : (y : X) ∈ closure A := by
        simpa [h_closureA_univ] using hy
      exact h_subset this
    exact Set.Subset.antisymm (Set.subset_univ _) h_univ_subset
  -- Step 3: `interior (closure B)` is `univ`.
  have h_int_eq : interior (closure B) = (Set.univ : Set X) := by
    simpa [h_closureB_univ, interior_univ]
  -- Step 4: the desired membership is now immediate.
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h_int_eq] using this

theorem P3_prod_univ_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P3 (A := A)) : Topology.P3 (A := Set.prod A (Set.univ : Set Y)) := by
  -- `Set.univ : Set Y` satisfies `P3`.
  have hB : Topology.P3 (A := (Set.univ : Set Y)) := by
    simpa using Topology.P3_univ (X := Y)
  simpa using
    Topology.P3_prod (A := A) (B := (Set.univ : Set Y)) hA hB