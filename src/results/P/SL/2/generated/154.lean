

theorem Topology.interior_inter_eq {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B : Set X) = interior A ∩ interior B := by
  apply subset_antisymm
  ·
    intro x hx
    -- `interior (A ∩ B)` is contained in both `interior A` and `interior B`
    have hA : (interior (A ∩ B : Set X) : Set X) ⊆ interior A := by
      have hSub : ((A ∩ B) : Set X) ⊆ (A : Set X) := by
        intro y hy
        exact hy.1
      exact interior_mono hSub
    have hB : (interior (A ∩ B : Set X) : Set X) ⊆ interior B := by
      have hSub : ((A ∩ B) : Set X) ⊆ (B : Set X) := by
        intro y hy
        exact hy.2
      exact interior_mono hSub
    exact And.intro (hA hx) (hB hx)
  ·
    intro x hx
    -- The reverse inclusion is given by an existing lemma.
    have hsubset :
        (interior A ∩ interior B : Set X) ⊆ interior (A ∩ B : Set X) :=
      interior_inter_subset (A := A) (B := B)
    exact hsubset hx