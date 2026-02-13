

theorem Topology.subset_closure_union_closure {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∪ closure (B : Set X) ⊆ closure (A ∪ B : Set X) := by
  intro x hx
  rcases hx with hxA | hxB
  ·
    have : (x : X) ∈ closure (A ∪ B : Set X) :=
      (closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)) hxA
    exact this
  ·
    have : (x : X) ∈ closure (A ∪ B : Set X) :=
      (closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)) hxB
    exact this