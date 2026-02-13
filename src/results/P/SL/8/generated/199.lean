

theorem P1_subset_closureInterior_of_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1 : Topology.P1 A) (hcl : closure A ⊆ B) :
    A ⊆ closure (interior B) := by
  -- First derive the simpler inclusion `A ⊆ B`.
  have hAB : A ⊆ B := by
    intro x hxA
    exact hcl (subset_closure hxA)
  -- Apply the existing lemma that works with a direct subset.
  exact
    Topology.P1_subset_closureInterior_of_subset (X := X)
      (A := A) (B := B) hP1 hAB