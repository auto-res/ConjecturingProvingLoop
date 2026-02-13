

theorem Topology.dense_interior_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P3 A := by
  intro hDenseInt
  intro x hxA
  -- `closure (interior A) = univ`
  have hCl_eq_univ : closure (interior (A : Set X)) = (Set.univ : Set X) :=
    hDenseInt.closure_eq
  -- hence `interior (closure (interior A)) = univ`
  have hInt_eq_univ :
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
    simpa [hCl_eq_univ, interior_univ]
  -- and so `univ ⊆ interior (closure A)`
  have hSub_univ :
      (Set.univ : Set X) ⊆ interior (closure (A : Set X)) := by
    intro y hy
    have : y ∈ interior (closure (interior (A : Set X))) := by
      simpa [hInt_eq_univ] using hy
    exact
      (Topology.interior_closure_interior_subset_interior_closure (A := A)) this
  -- therefore `interior (closure A) = univ`
  have hIntCl_eq_univ :
      interior (closure (A : Set X)) = (Set.univ : Set X) := by
    apply subset_antisymm
    · intro y hy; simp
    · exact hSub_univ
  -- conclude `x ∈ interior (closure A)`
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hIntCl_eq_univ] using this