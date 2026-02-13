

theorem P1_subset_closureInterior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) :
    A ⊆ closure (interior (closure A)) := by
  have hSub : A ⊆ closure A := subset_closure
  exact
    P1_subset_closureInterior_of_subset (X := X) (A := A) (B := closure A) hP1 hSub