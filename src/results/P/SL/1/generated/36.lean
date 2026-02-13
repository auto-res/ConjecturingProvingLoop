

theorem Topology.closure_eq_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure A = closure (interior A) := by
  intro hP2
  apply Set.Subset.antisymm
  ·
    -- First, `closure A ⊆ closure (interior (closure (interior A)))`
    have h1 : closure A ⊆ closure (interior (closure (interior A))) :=
      closure_mono hP2
    -- Next, `closure (interior (closure (interior A))) ⊆ closure (interior A)`
    have h2 : closure (interior (closure (interior A))) ⊆ closure (interior A) := by
      have hinner : interior (closure (interior A)) ⊆ closure (interior A) :=
        interior_subset
      have hclosure : closure (interior (closure (interior A))) ⊆
          closure (closure (interior A)) :=
        closure_mono hinner
      simpa [closure_closure] using hclosure
    exact Set.Subset.trans h1 h2
  ·
    -- The reverse inclusion `closure (interior A) ⊆ closure A`
    have hsub : interior A ⊆ (A : Set X) := interior_subset
    exact closure_mono hsub